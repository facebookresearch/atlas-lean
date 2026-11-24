# One greedy step

Let $C$ be a linear code of length $n$ over a finite field $F$ with $q$ elements whose nonzero
codewords all have weight at least $d \ge 1$. If

$$q^{\dim C} \cdot \mathrm{Vol}_q(n, d-1) < q^n,$$

then there is a linear code $C' \supseteq C$ with $\dim C' = \dim C + 1$ whose nonzero codewords
all have weight at least $d$.

The balls of radius $d - 1$ around the $q^{\dim C}$ codewords miss some word $v$; then
$C' = C + Fv$. A nonzero word $c + av$ of $C'$ with $a \ne 0$ is $a(v - c')$ with
$c' = -a^{-1} c \in C$, so its weight is the distance from $v$ to $c'$, at least $d$.

## Background

- [Size of a Hamming ball](card-ball.md): the count of the words covered by the balls.

## Sources

- R. R. Varshamov, "Estimate of the number of signals in error correcting codes", *Doklady Akademii Nauk SSSR* 117 (1957), 739–741.
- V. Guruswami, A. Rudra, M. Sudan, *Essential Coding Theory*, draft of August 26, 2025, Theorem 4.2.1 (linear part, proved there with a random generator matrix).
