# Evaluation of IMP Boolean expressions

The truth value of a Boolean expression in a
state $\sigma : \mathbb{N} \to \mathbb{N}$ is defined by recursion on the expression: the
constants true and false have values true and false; for arithmetic expressions $a_1$ and $a_2$,
the comparison $a_1 = a_2$ is true exactly when the values of $a_1$ and $a_2$ in $\sigma$ are
equal, and $a_1 \le a_2$ is true exactly when the value of $a_1$ is at most the value of $a_2$;
for Boolean expressions $b$, $b_1$ and $b_2$, the negation $\neg b$ is true exactly when $b$ is
false, and the conjunction $b_1 \wedge b_2$ is true exactly when both $b_1$ and $b_2$ are true.
