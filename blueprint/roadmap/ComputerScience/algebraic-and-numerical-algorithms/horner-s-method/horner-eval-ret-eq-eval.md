# Horner evaluation is polynomial evaluation

For every commutative semiring $R$,
every $x \in R$ and all coefficients $a_0, \dots, a_{n-1} \in R$, the value returned by Horner
evaluation of $a_0, \dots, a_{n-1}$ at $x$ equals $p(x)$, where
$p = a_0 + a_1 X + \dots + a_{n-1} X^{n-1} \in R[X]$ is the polynomial with these
coefficients.
