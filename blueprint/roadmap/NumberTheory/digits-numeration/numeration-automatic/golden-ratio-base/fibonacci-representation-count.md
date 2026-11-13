# Number of Fibonacci representations

For a natural number $m$,
$\mathrm{Tot}_{\mathrm{FIB}}(m)$ is the number of finite sets $T$ of indices $i \ge 2$ with
$\sum_{i \in T} F_i = m$, where $F_i$ are the Fibonacci numbers ($F_0 = 0$, $F_1 = 1$); that is,
the number of ways to write $m$ as a sum of Fibonacci numbers with distinct indices at least $2$
(OEIS A000119). Indices above $m + 1$ never occur because $F_{m+2} > m$.

## Sources

- Michel Dekking and Ad van Loon, *Counting Base Phi Representations*, Fibonacci Quarterly 62 (2024), Section 1 (base Fibonacci representations).
