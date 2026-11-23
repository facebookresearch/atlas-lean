# Return to the initial coefficient vector modulo $p^a$

Let $p$ be a prime, let
$a, m \in \mathbb{N}$, and let $\tilde P$ be a Laurent polynomial with integer coefficients in
variables $x_1, \dots, x_r$ such that for every $j \in \mathbb{Z}^r$ the coefficients of $x^j$ in
$\tilde P(x_1, \dots, x_r)^p$ and in $\tilde P(x_1^p, \dots, x_r^p)$ are congruent modulo $p^a$.
Suppose $\deg \tilde P \le m + 1$, where $\deg \tilde P$ is the largest absolute value of an
exponent of a single variable in a monomial occurring in $\tilde P$ (and $0$ if $\tilde P = 0$),
and let $T = \{-m, \dots, m\}^r$. Then there is $t_0 \in \mathbb{N}$ such that for every
$n \in \mathbb{N}$ for which $p$ does not divide the constant term of $\tilde P^n$, there is
$j < p^{t_0}$ such that for every $i \in T$ the coefficient of $x^{-i}$ in
$\tilde P^{p^{t_0} n + j}$ is congruent modulo $p^a$ to $1$ if $i = 0$ and to $0$ otherwise.

Equivalently, writing $\tilde V(n)$ for the vector of coefficients of $x^{-i}$ in $\tilde P^n$,
$i \in T$, reduced modulo $p^a$, some $\tilde V(p^{t_0} n + j)$ with $j < p^{t_0}$ equals
$\tilde V(0)$. This is the analogue modulo $p^a$ of Proposition 15.

## Sources

- Nadav Kohen, *A Linear Representation for Constant Term Sequences mod p^a with Applications to Uniform Recurrence*, Journal of Integer Sequences 29 (2026), Article 26.4.2, Proposition 32 (`jis-2026-26.4.2-prop-32`).
