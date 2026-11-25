# Evaluation of IMP arithmetic expressions

The value of an arithmetic expression in a state
$\sigma : \mathbb{N} \to \mathbb{N}$ is the natural number defined by recursion on the expression:
a constant $n$ has value $n$, the variable $x_i$ with index $i$ has value $\sigma(i)$, and for
arithmetic expressions $a_1$ and $a_2$, the expressions $a_1 + a_2$, $a_1 - a_2$ and
$a_1 \cdot a_2$ have as value the sum, the truncated difference and the product of the values of
$a_1$ and $a_2$. The truncated difference of natural numbers $m$ and $n$ is $\max(m - n, 0)$.
