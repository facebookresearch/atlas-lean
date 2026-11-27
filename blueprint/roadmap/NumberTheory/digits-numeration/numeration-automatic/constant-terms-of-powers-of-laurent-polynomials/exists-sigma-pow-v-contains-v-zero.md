# Return to the initial coefficient vector modulo $p$

Let $p$ be a prime, let
$m \in \mathbb{N}$, and let $P$ be a Laurent polynomial with integer coefficients in variables
$x_1, \dots, x_r$ with $\deg P \le m + 1$, where $\deg P$ is the largest absolute value of an
exponent of a single variable in a monomial occurring in $P$ (and $0$ if $P = 0$). Let
$T = \{-m, \dots, m\}^r$. Then there is $t_0 \in \mathbb{N}$ such that for every $n \in \mathbb{N}$
for which $p$ does not divide the constant term of $P^n$, there is $j < p^{t_0}$ such that for
every $i \in T$ the coefficient of $x^{-i}$ in $P^{p^{t_0} n + j}$ is congruent modulo $p$ to $1$
if $i = 0$ and to $0$ otherwise.

Equivalently, writing $V(n)$ for the vector of coefficients of $x^{-i}$ in $P^n$, $i \in T$,
reduced modulo $p$, the block $V(p^{t_0} n), \dots, V(p^{t_0} n + p^{t_0} - 1)$ contains $V(0)$.

## Sources

- Nadav Kohen, *A Linear Representation for Constant Term Sequences mod p^a with Applications to Uniform Recurrence*, Journal of Integer Sequences 29 (2026), Article 26.4.2, Proposition 15 (`jis-2026-26.4.2-prop-15`).
