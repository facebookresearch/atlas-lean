# Recurrence for the $r$-associated Stirling Eulerian numbers

For natural numbers $r$, $n$,
$m$ let $A^r_{n,m}$ be the number of permutations $\sigma$ of $\{0, \dots, n-1\}$ with exactly
$m$ excedances (points $i$ with $\sigma(i) > i$) all of whose cycles (fixed points counted as
cycles of length one) have length greater than $r$, and for natural numbers $a$, $b$ let
$C_{a,b}$ be the circular Eulerian number, the number of permutations of $\{0, \dots, a-1\}$,
$a \ge 1$, that consist of a single cycle through all points and have exactly $b$ excedances
($C_{0,b} = 0$). If $m \le n$ and $n \ge r + 1$, then

$$A^r_{n,m} = m A^r_{n-1,m} + (n-m) A^r_{n-1,m-1} +
\binom{n-1}{r} \sum_{s=0}^{m} C_{r+1,s} A^r_{n-r-1,m-s},$$

where the term $(n-m) A^r_{n-1,m-1}$ is read as $0$ when $m = 0$.

## Sources

- Imboa-Navalona Manjaka Rakotoson and Fanja Rakotondrajao, *Associated Stirling Eulerian Numbers and Their q-Analogues*, Journal of Integer Sequences 28 (2025), Article 25.5.7, Theorem 30 (`jis-2025-25.5.7-thm-30`).
