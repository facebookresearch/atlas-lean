# Compilation of arithmetic expressions

The compiled code of an arithmetic expression is
the list of stack-machine instructions defined by recursion: a constant $n$ compiles to the
single instruction push $n$, a variable $x$ to the single instruction load $x$, and the sum,
difference or product of $a_1$ and $a_2$ to the code of $a_1$, then the code of $a_2$, then the
single instruction add, sub or mul respectively.

Running this code leaves the value of the expression on top of the stack.
