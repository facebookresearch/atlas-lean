# Compilation of Boolean expressions

The compiled code of a Boolean expression is the list
of stack-machine instructions defined by recursion, using the compiled code of arithmetic
expressions: the truth value true compiles to the single instruction push $1$ and false to push
$0$; the test $a_1 = a_2$ (respectively $a_1 \le a_2$) compiles to the code of $a_1$, then the
code of $a_2$, then the equality (respectively order) test instruction; the negation of $b_1$
compiles to the code of $b_1$ followed by the negation instruction; and the conjunction of $b_1$
and $b_2$ compiles to the code of $b_1$, then the code of $b_2$, then the conjunction instruction.

Running this code leaves $1$ (true) or $0$ (false) on top of the stack.
