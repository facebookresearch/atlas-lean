# Extending a Farey path extends the continued fraction

Let $F$ be a field, let $n \ge 1$,
and let $a_0, a_1, \dots, a_n \in F[X]$ with $a_i$ nonconstant for $1 \le i \le n$. Let
$A_0, \dots, A_n, B_0, \dots, B_n \in F[X]$ be such that, for every $i \le n$, $A_i$ and $B_i$ are
the numerator and the denominator of the $i$th convergent of the continued fraction
$[a_0, a_1, \dots, a_n]$ over $F(X)$. Let $u, v \in F[X]$ be such that $u B_n - v A_n$ is a unit
of $F[X]$ (a nonzero constant) and $\deg B_n < \deg v$. Then there is a nonconstant polynomial
$b \in F[X]$ such that, in $F(X)$,

$$b = \frac{v A_{n-1} - u B_{n-1}}{u B_n - v A_n},$$

and the $(n+1)$st convergent of the continued fraction $[a_0, a_1, \dots, a_n, b]$ equals $u/v$.

Compared with the paper: the case $n = 0$, which needs $A_{-1} = 1$ and $B_{-1} = 0$, is excluded;
the paper's degree condition on the reduced denominator of $A_n / B_n$ is stated with $B_n$ itself
(the two agree, since $A_n / B_n$ is already in lowest terms); and the hypothesis that $u$ and $v$
are coprime is omitted, since adjacency implies it.

## Sources

- Tuangrat Chaichana, Arlisa Janjing and Teeraphong Phongpattanacharoen, *An Interpretation of Continued Fractions and Farey Graphs in the Field of Rational Functions*, INTEGERS 26 (2026), Article A3, Theorem 5.
