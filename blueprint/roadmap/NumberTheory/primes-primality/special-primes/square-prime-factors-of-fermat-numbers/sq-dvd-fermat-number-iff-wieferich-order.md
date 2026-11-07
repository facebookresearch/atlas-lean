# Squared prime factors of Fermat numbers via Wieferich primes and orders

Let
$F_n = 2^{2^n} + 1$ be the $n$-th Fermat number. For every natural number $n$ and every odd prime
$p$, $p^2$ divides $F_n$ if and only if $p$ is a Wieferich prime (to base $2$) and the
multiplicative order of $2$ modulo $p$ is $2^{n+1}$.

This follows from the criterion that a prime $p$ dividing $F_n$ satisfies $p^2 \mid F_n$ exactly
when $2^{p-1} \equiv 1 \pmod{p^2}$, since an odd prime $p$ divides $F_n$ exactly when the order
of $2$ modulo $p$ is $2^{n+1}$.

## Sources

- Klaška, *Several Notes on Jakóbczyk's Hypothesis on Fermat Numbers*, INTEGERS 26 (2026), Article A77, Theorem 5, Equation (11) (`integers-2026-A77-thm-5`).
