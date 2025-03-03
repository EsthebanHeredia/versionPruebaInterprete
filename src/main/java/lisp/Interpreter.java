package lisp;

import lisp.data.Number;
import lisp.data.*;
import lisp.exceptions.InvalidArgumentException;
import lisp.exceptions.*;
import lisp.parser.Parser;

import java.io.*;
import java.util.Collections;

import static lisp.data.Number.*;
import static lisp.data.Symbol.*;

public class Interpreter {

    private boolean trace = false;
    private SExpression globalEnv = NIL;
    private InputStream inputStream = System.in;
    private PrintStream printStream = System.out;

    private int traceLevel = 0;

    Interpreter() {
        this(new String[0]);
    }

    Interpreter(String[] args) {
        // Initialize parameters as a list in the global environment
        SExpression paramList = NIL;
        // Add parameters in reverse to build the list correctly
        for (int i = args.length - 1; i >= 0; i--) {
            paramList = cons(LispString.string(args[i]), paramList);
        }
        try {
            // Store parameters in global environment under the PARAMS symbol
            globalEnv = cons(cons(PARAMS, paramList), globalEnv);
        } catch (Exception e) {
            // Handle any exceptions during initialization
            printStream.println("Error initializing parameters: " + e.getMessage());
        }
    }

    public static void main(String[] args) throws LispException {
        Interpreter interpreter = new Interpreter(args);
        interpreter.readEvalPrintLoop();
    }

    void readEvalPrintLoop() {
        readEvalPrintLoop(inputStream, printStream);
    }

    void readEvalPrintLoop(InputStream inputStream, PrintStream printStream) {
        BufferedReader br = new BufferedReader(new InputStreamReader(inputStream));
        Parser parser = null;
        try {
            parser = new Parser(br);
        } catch (LispIOException e) {
            printStream.println(e.getMessage());
            return;
        }
        SExpression expression;
        SExpression value;
        while (true) {
            try {
                // Print prompt only for interactive sessions (when using System.in)
                if (inputStream == System.in) {
                    printStream.print("> ");
                }

                expression = parser.read();
                if (expression == null) {
                    printStream.println("incorrect syntax");
                } else if (expression == NIL) {
                    return;
                } else {
                    // Show the expression if tracing is enabled
                    if (trace) {
                        printStream.print("Expression: ");
                        expression.print(printStream);
                        printStream.println();
                    }

                    try {
                        value = eval(expression, globalEnv);

                        // Only print result if it wasn't handled by a print function
                        if (!(expression.isAtom() ||
                                (car(expression) == PRINT ||
                                        car(expression) == PRINC ||
                                        car(expression) == PRINT_IF ||
                                        car(expression) == PRINT_UNLESS))) {
                            printStream.print("Result: ");
                            value.print(printStream);
                            printStream.println();
                        }
                    } catch (LispException e) {
                        printStream.println("exception: " + e.getMessage());
                    }
                }
            } catch (ParsingException e) {
                printStream.println("parsing exception: " + e.getMessage());
            } catch (LispException e) {
                printStream.println("exception: " + e.getMessage());
            }
        }
    }

    public static SExpression cons(SExpression car, SExpression cdr) {
        return new Cons(car, cdr);
    }

    private static SExpression car(SExpression expr) throws InvalidArgumentException { return expr.car(); }
    private static SExpression cdr(SExpression expr) throws InvalidArgumentException { return expr.cdr(); }
    private static SExpression caar(SExpression expr) throws InvalidArgumentException { return car(car(expr)); }
    private static SExpression cadr(SExpression expr) throws InvalidArgumentException { return car(cdr(expr)); }
    private static SExpression cdar(SExpression expr) throws InvalidArgumentException { return cdr(car(expr)); }
    private static SExpression cddr(SExpression expr) throws InvalidArgumentException { return cdr(cdr(expr)); }
    private static SExpression cadar(SExpression expr) throws InvalidArgumentException { return car(cdar(expr)); }
    private static SExpression caddr(SExpression expr) throws InvalidArgumentException { return car(cddr(expr)); }
    private static SExpression cdddr(SExpression expr) throws InvalidArgumentException { return cdr(cddr(expr)); }
    private static SExpression cadddr(SExpression expr) throws InvalidArgumentException { return car(cdddr(expr)); }

    /*
        eval evaluates an expression in the context of an environment, which is an association between symbols and
        their values, represented as a list of dotted pairs (or association list).
     */
    SExpression eval(SExpression expr, SExpression env) throws LispException {
        SExpression value;
        if (trace) traceEvalEntry(expr, env);
        if (expr.isSymbol()) {
            // T and NIL are special symbols that always evaluate to themselves
            if (T == expr || NIL == expr) value = expr;
                // for all other symbols, their value is found in the environment association list
            else value = assoc((Symbol) expr, env);
        } else if (expr.isNumber()) value = expr;    // numbers evaluate to themselves
        else if (expr.isString()) value = expr;     // strings evaluate to themselves
        else {
            // if not a symbol or number, it's an sexpression (symbolic expression), which should be a list,
            // where the first element (car) is a function (or special form)
            SExpression func = car(expr);
            // special forms are handled first
            // these are exceptions to the general rule (which is: evaluate arguments, apply the function)
            if (func == QUOTE) value = cadr(expr);
            else if (func == BACKQUOTE) value = evalCommas(cadr(expr), env);
            else if (func == IF)
                value = (T == eval(cadr(expr), env)) ? eval(caddr(expr), env) : eval(cadddr(expr), env);
            else if (func == COND) value = evalConditional(cdr(expr), env);
            else if (func == AND) value = evalAnd(cdr(expr), env);
            else if (func == OR) value = evalOr(cdr(expr), env);
            else if (func == SETQ) value = performSetq((Symbol) cadr(expr), eval(caddr(expr), env));
            else if (func == DEFUN) value = performDefun((Symbol) cadr(expr), caddr(expr), cadddr(expr));
            else if (func == DEFMACRO) value = performDefmacro((Symbol) cadr(expr), caddr(expr), cadddr(expr));
            else if (func == LAMBDA) value = cons(CLOSURE, cons(expr, cons(env, NIL)));
            else if (func == LOAD) value = loadFile(cadr(expr));
                // Case statement handling
            else if (func == CASE) {
                SExpression keyExpr = eval(cadr(expr), env);
                SExpression clauses = cddr(expr);
                value = NIL;

                // Process each clause until a match is found
                while (clauses != NIL) {
                    SExpression clause = car(clauses);
                    SExpression keyList = car(clause);
                    SExpression body = cadr(clause);

                    // Check if this is the default/otherwise case (T)
                    if (keyList == T) {
                        value = eval(body, env);
                        break;
                    }

                    // If keyList is an atom, convert it to a list for uniform processing
                    if (keyList.isAtom()) {
                        keyList = cons(keyList, NIL);
                    }

                    // Check each key in the keyList
                    SExpression currentKey = keyList;
                    boolean matched = false;

                    while (currentKey != NIL) {
                        if (equal(keyExpr, car(currentKey))) {
                            matched = true;
                            break;
                        }
                        currentKey = cdr(currentKey);
                    }

                    if (matched) {
                        value = eval(body, env);
                        break;
                    }

                    // Move to next clause
                    clauses = cdr(clauses);
                }
            }
            // Print functions - handle them as special forms to avoid evaluating their arguments
            else if (func == PRINT) {
                SExpression arg = cadr(expr);
                SExpression result = eval(arg, env);
                result.print(printStream);
                printStream.println();
                value = result;
            }
            else if (func == PRINC) {
                SExpression arg = cadr(expr);
                SExpression result = eval(arg, env);
                // For strings, we want to print without quotation marks
                if (result.isString()) {
                    printStream.print(((LispString)result).value());
                } else {
                    result.print(printStream);
                }
                value = result;
            }
            else if (func == PRINT_IF) {
                SExpression condition = eval(cadr(expr), env);
                if (condition != NIL) {
                    SExpression result = eval(caddr(expr), env);
                    result.print(printStream);
                    printStream.println();
                    value = result;
                } else {
                    value = NIL;
                }
            }
            else if (func == PRINT_UNLESS) {
                SExpression condition = eval(cadr(expr), env);
                if (condition == NIL) {
                    SExpression result = eval(caddr(expr), env);
                    result.print(printStream);
                    printStream.println();
                    value = result;
                } else {
                    value = NIL;
                }
            }
            else if (func.isSymbol()) {
                SExpression funcVal = assoc((Symbol) func, env);
                if (!funcVal.isAtom() && car(funcVal) == MACRO) {
                    SExpression macroParams = cadr(funcVal);
                    SExpression macroBody = caddr(funcVal);
                    SExpression expandedMacro = expandMacro(macroParams, cdr(expr), macroBody, env);
                    value = eval(expandedMacro, env);
                } else value = apply(func, map((s) -> (eval(s, env)), cdr(expr)), env);
            } else if (func.isAtom()) {
                throw new InvalidFunctionException(func.toString() + " is not a function");
            } else value = apply(func, map((s) -> (eval(s, env)), cdr(expr)), env);
        }
        if (trace) traceEvalReturn(value);
        return value;
    }

    SExpression eval(SExpression expr) throws LispException {
        return eval(expr, this.globalEnv);
    }

    SExpression apply(SExpression function, SExpression argValues, SExpression env) throws LispException {
        SExpression value;
        if (trace) traceApplyEntry(function, argValues, env);
        if (function.isSymbol()) {
            if (function == TRACE) {
                trace = true;
                value = TRACE;
            } else if (function == UNTRACE) {
                trace = false;
                value = UNTRACE;
            } else if (function == CAR) value = car(consCheck(car(argValues)));
            else if (function == CDR) value = cdr(consCheck(car(argValues)));
            else if (function == CONS) value = cons(car(argValues), cadr(argValues));
            else if (function == LIST) value = argValues;
            else if (function == NULL) value = car(argValues) == NIL ? T : NIL;
            else if (function == NOT) value = car(argValues) == NIL ? T : NIL;
            else if (function == EQ) value = car(argValues) == cadr(argValues) ? T : NIL;
            else if (function == ATOM) value = car(argValues).isAtom() ? T : NIL;
                // Add LISTP, EQUAL, LT, GT predicates
            else if (function == LISTP) value = isListp(car(argValues)) ? T : NIL;
            else if (function == EQUAL) value = equal(car(argValues), cadr(argValues)) ? T : NIL;
            else if (function == LT) value = (numberValue(car(argValues)) < numberValue(cadr(argValues))) ? T : NIL;
            else if (function == GT) value = (numberValue(car(argValues)) > numberValue(cadr(argValues))) ? T : NIL;
            else if (function == EQ_NUM) {
                SExpression arg1 = car(argValues);
                SExpression arg2 = cadr(argValues);

                // Check for numeric args
                numberCheck(arg1);
                numberCheck(arg2);

                value = (numberValue(arg1) == numberValue(arg2)) ? T : NIL;
            }
            else if (function == SYMBOLP) value = car(argValues).isSymbol() ? T : NIL;
            else if (function == NUMBERP) value = car(argValues).isNumber() ? T : NIL;
            else if (function == SUB1) value = number(numberValue(car(argValues)) - 1);
            else if (function == ADD1) value = number(numberValue(car(argValues)) + 1);
            else if (function == ZEROP) value = car(argValues) == ZERO ? T : NIL;
            else if (function == LESSP) value = (numberValue(car(argValues)) < numberValue(cadr(argValues))) ? T : NIL;
            else if (function == GREATERP) value = (numberValue(car(argValues)) > numberValue(cadr(argValues))) ? T : NIL;
            else if (function == TIMES) value = reduce(argValues, (n, m) -> number(numberValue(n) * numberValue(m)), ONE);
            else if (function == PLUS) value = reduce(argValues, (n, m) -> number(numberValue(n) + numberValue(m)), ZERO);
            else if (function == MINUS) value = number(numberValue(car(argValues)) - numberValue(cadr(argValues)));
            else if (function == DIV) value = number(numberValue(car(argValues)) / numberValue(cadr(argValues)));
            else if (function == DIVIDE) {
                SExpression dividend = car(argValues);
                SExpression divisor = cadr(argValues);

                // Check for numeric args
                numberCheck(dividend);
                numberCheck(divisor);

                // Check for division by zero
                if (numberValue(divisor) == 0) {
                    throw new InvalidArgumentException("division by zero");
                }

                // Perform division
                value = number(numberValue(dividend) / numberValue(divisor));
            }
            else if (function == MOD) value = number(numberValue(car(argValues)) % numberValue(cadr(argValues)));
            else if (function == EVAL) value = eval(car(argValues), env);
            else {
                SExpression fVal = assoc((Symbol) function, env);
                if (fVal == NIL) throw new InvalidFunctionException("undefined function " + function.toString());
                value = apply(fVal, argValues, env);
            }
        } else if (car(function) == LAMBDA)
            value = eval(caddr(function), biMap(Interpreter::cons, cadr(function), argValues, env));
        else if (car(function) == CLOSURE) value = apply(cadr(function), argValues, caddr(function));
        else if (car(function) == MACRO) value = apply(cadr(function), argValues, caddr(function));
        else {
            SExpression evaledFunction = eval(function, env);
            if (evaledFunction == function) throw new InvalidFunctionException("could not resolve function");
            value = apply(evaledFunction, argValues, env);
        }
        if (trace && value != TRACE) traceApplyReturn(value);
        return value;
    }

    // Helper methods for predicates
    private boolean isListp(SExpression expr) throws LispException {
        if (expr == NIL) return true;
        if (expr.isAtom()) return false;
        try {
            return isListp(cdr(expr));
        } catch (InvalidArgumentException e) {
            return false;
        }
    }

    private boolean equal(SExpression expr1, SExpression expr2) throws LispException {
        // If they're the same object, they're equal
        if (expr1 == expr2) return true;

        // If one is atom but other isn't, they're not equal
        if (expr1.isAtom() != expr2.isAtom()) return false;

        // If they're both atoms
        if (expr1.isAtom()) {
            // If one is symbol and other isn't, they're not equal
            if (expr1.isSymbol() != expr2.isSymbol()) return false;
            // If one is number and other isn't, they're not equal
            if (expr1.isNumber() != expr2.isNumber()) return false;
            // If one is string and other isn't, they're not equal
            if (expr1.isString() != expr2.isString()) return false;

            // Compare values based on type
            if (expr1.isSymbol()) {
                // Symbols are compared by reference, which was handled earlier
                return false; // Should not reach here
            } else if (expr1.isNumber()) {
                return numberValue(expr1) == numberValue(expr2);
            } else if (expr1.isString()) {
                return ((LispString)expr1).value().equals(((LispString)expr2).value());
            }
            return false;
        }

        // Both are cons cells, compare CAR and CDR
        try {
            return equal(car(expr1), car(expr2)) && equal(cdr(expr1), cdr(expr2));
        } catch (InvalidArgumentException e) {
            return false;
        }
    }

    private void traceApplyEntry(SExpression function, SExpression argValues, SExpression env) {
        traceLevel++;
        printStream.print(indent() + ">APPLY: ");
        function.print(printStream);
        printStream.print("  ");
        argValues.print(printStream);
        printStream.println();
    }

    private void traceApplyReturn(SExpression value) {
        printStream.print(indent() + "<APPLY: ");
        value.print(printStream);
        printStream.println();
        traceLevel--;
    }

    private void traceEvalEntry(SExpression expr, SExpression env) {
        traceLevel++;
        printStream.print(indent() + ">EVAL: ");
        expr.print(printStream);
        printStream.println();
    }

    private void traceEvalReturn(SExpression value) {
        printStream.print(indent() + "<EVAL: ");
        value.print(printStream);
        printStream.println();
        traceLevel--;
    }

    private String indent() {
        return String.join("", Collections.nCopies(traceLevel, " "));
    }

    private SExpression assoc(Symbol s, SExpression alist) throws InvalidArgumentException {
        if (alist == NIL) return NIL;
        else if (caar(alist) == s) return cdar(alist);
        else return assoc(s, cdr(alist));
    }

    private SExpression append(SExpression list1, SExpression list2) throws InvalidArgumentException {
        return list1 == NIL ? list2 : cons(car(list1), append(cdr(list1), list2));
    }

    private SExpression evalConditional(SExpression conds, SExpression env) throws LispException {
        if (NIL == conds) return NIL;
        else if (T == eval(caar(conds), env)) return eval(cadar(conds), env);
        else return evalConditional(cdr(conds), env);
    }

    private SExpression evalAnd(SExpression args, SExpression env) throws LispException {
        if (NIL == args) return T;
        else if (eval(car(args), env) == NIL) return NIL;
        else return evalAnd(cdr(args), env);
    }

    private SExpression evalOr(SExpression args, SExpression env) throws LispException {
        if (NIL == args) return NIL;
        else if (eval(car(args), env) != NIL) return T;
        else return evalOr(cdr(args), env);
    }

    private SExpression evalCommas(SExpression expr, SExpression env) throws LispException {
        if (expr.isAtom()) return expr;
        else if (car(expr) == COMMA) return eval(cadr(expr), env);
        else if (!car(expr).isAtom() && caar(expr) == COMMA_AT) return append(eval(cadar(expr), env), evalCommas(cdr(expr), env));
        else return cons(evalCommas(car(expr), env), evalCommas(cdr(expr), env));
    }

    private SExpression expandMacro(SExpression params, SExpression argExprs, SExpression body, SExpression env) throws LispException {
        if (trace) traceExpandMacroEntry(params, argExprs, body, env);
        SExpression value = eval(body, biMap(Interpreter::cons, params, argExprs, env));
        if (trace) traceExpandMacroReturn(value);
        return value;
    }

    private void traceExpandMacroEntry(SExpression params, SExpression argExprs, SExpression body, SExpression env) {
        traceLevel++;
        printStream.print(indent() + ">EXPAND MACRO: ");
        params.print(printStream);
        printStream.print("  ");
        argExprs.print(printStream);
        printStream.print("  ");
        body.print(printStream);
        printStream.println();
    }

    private void traceExpandMacroReturn(SExpression value) {
        printStream.print(indent() + "<EXPAND MACRO: ");
        value.print(printStream);
        printStream.println();
        traceLevel--;
    }

    private SExpression performSetq(Symbol sym, SExpression val) throws InvalidArgumentException {
        globalEnv = updateEnv(sym, val, globalEnv);
        return val;
    }

    private SExpression performDefun(Symbol fname, SExpression vars, SExpression body) throws InvalidArgumentException {
        SExpression lambdaExpr = cons(LAMBDA, cons(vars, cons(body, NIL)));
        globalEnv = updateEnv(fname, lambdaExpr, globalEnv);
        return lambdaExpr;
    }

    private SExpression performDefmacro(Symbol fname, SExpression vars, SExpression body) throws InvalidArgumentException {
        SExpression macroDef = cons(MACRO, cons(vars, cons(body, NIL)));
        globalEnv = updateEnv(fname, macroDef, globalEnv);
        return macroDef;
    }

    private SExpression updateEnv(Symbol sym, SExpression val, SExpression env) throws InvalidArgumentException {
        if (env == NIL) return cons(cons(sym, val), NIL);
        else if (sym == caar(env)) return cons(cons(sym, val), cdr(env));
        else return cons(car(env), updateEnv(sym, val, cdr(env)));
    }

    private SExpression map(CheckedFunction<SExpression, SExpression> f, SExpression list) throws LispException {
        if (list == NIL) return NIL;
        else return cons(f.apply(car(list)), map(f, cdr(list)));
    }

    private SExpression biMap(CheckedBiFunction<SExpression, SExpression, SExpression> f, SExpression list1, SExpression list2, SExpression env) throws LispException {
        if (list1 == NIL || list2 == NIL) return env;
        else return cons(f.apply(car(list1), car(list2)), biMap(f, cdr(list1), cdr(list2), env));
    }

    private SExpression reduce(SExpression list, CheckedBiFunction<SExpression, SExpression, SExpression> f, SExpression identity) throws LispException {
        if (list == NIL) return identity;
        else return f.apply(car(list), reduce(cdr(list), f, identity));
    }

    private SExpression consCheck(SExpression argVal) throws LispException {
        if (argVal.isAtom()) throw new InvalidArgumentException("atomic argument: " + argVal.toString());
        else return argVal;
    }

    private SExpression numberCheck(SExpression argVal) throws LispException {
        if (!argVal.isNumber()) throw new InvalidArgumentException("non-numeric argument: " + argVal.toString());
        else return argVal;
    }

    private long numberValue(SExpression argVal) throws LispException {
        if (!argVal.isNumber()) throw new InvalidArgumentException("non-numeric argument: " + argVal.toString());
        else return ((Number)argVal).value();
    }

    @FunctionalInterface
    public interface CheckedFunction<T, R> {
        R apply(T t) throws LispException;
    }

    @FunctionalInterface
    public interface CheckedBiFunction<T, U, R> {
        R apply(T t, U u) throws LispException;
    }

    private SExpression loadFile(SExpression filename) throws LispException {
        if (!filename.isString()) throw new InvalidArgumentException("filename must be a string");
        String filenameString = ((LispString) filename).value();
        InputStream is;
        try {
            is = new FileInputStream(filenameString);
        } catch (FileNotFoundException e) {
            throw new LispIOException("file not found: " + filenameString);
        }
        readEvalPrintLoop(is, printStream);
        return T;
    }
}