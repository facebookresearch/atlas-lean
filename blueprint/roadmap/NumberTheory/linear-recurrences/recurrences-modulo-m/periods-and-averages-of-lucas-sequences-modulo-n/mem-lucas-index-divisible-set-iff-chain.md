# Smyth's description of the indices $n$ with $n \mid U_n$

Let $P, Q$ be coprime integers
with $Q \ne 0$ such that the Lucas pair $(P, Q)$ is nondegenerate, let $U = U(P, Q)$ be its Lucas
sequence, write $a = P$, $b = -Q$ (so that $U_{k+2} = a U_{k+1} + b U_k$) and $D = P^2 - 4Q$, and
let $T(U)$ be the set of positive integers $n$ coprime to $Q$ with $n \mid U_n$. Call $q_0$
admissible if $q_0 = 1$, or $q_0 = 6$ with $a \equiv 3$ and $b \equiv \pm 1 \pmod 6$, or
$q_0 = 12$ with $a \equiv \pm 1$ and $b \equiv 1 \pmod 6$. Call a finite list of primes
$q_1, \dots, q_r$ ($r \ge 0$, repetitions allowed) a chain from $q_0$ if
$q_i \mid D \, U_{q_0 q_1 \cdots q_{i-1}}$ for each $i$. Then every admissible $q_0$ lies in
$T(U)$; a natural number $n$ lies in $T(U)$ if and only if $n = q_0 q_1 \cdots q_r$ for some
admissible $q_0$ and some chain $q_1, \dots, q_r$ from $q_0$; for every admissible $q_0$ and every
chain $q_1, \dots, q_r$ from $q_0$, each product $q_0 q_1 \cdots q_i$ with $0 \le i \le r$ lies in
$T(U)$; and if $D = 1$, then $T(U) = \{1\}$.

## Sources

- Michal Křížek and Lawrence Somer, *Period Lengths Modulo n and Average of Terms of Second Order Linear Recurrences*, INTEGERS 24 (2024), Article A36, Theorem 4.1.
