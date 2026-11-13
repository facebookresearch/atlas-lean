# Recurrence for $r$-cycle Stirling Eulerian numbers

An excedance of a permutation
$\sigma$ of $\{0, \dots, N-1\}$ is an index $i$ with $\sigma(i) > i$. Let $A^{(r)}_{N,M}$ be the
number of permutations of $\{0, \dots, N-1\}$ with exactly $M$ excedances all of whose cycles,
fixed points included, have exactly $r$ elements, and let $C_{r,k}$ be the number of permutations
of $\{0, \dots, r-1\}$ with exactly $k$ excedances that consist of a single cycle through all $r$
points. Then for all natural numbers $r$, $n$, $m$ with $r \ge 2$ and $m \le n$,

$$A^{(r)}_{n+1,m} = \binom{n}{r-1} \sum_{k=1}^{m} C_{r,k}\, A^{(r)}_{n-(r-1),\,m-k},$$

where $n - (r-1)$ is truncated subtraction, equal to $0$ when $n < r - 1$ (harmless, since then
$\binom{n}{r-1} = 0$).

## Sources

- Imboa-Navalona Manjaka Rakotoson and Fanja Rakotondrajao, *Associated Stirling Eulerian Numbers and Their q-Analogues*, Journal of Integer Sequences 28 (2025), Article 25.5.7, Theorem 20 (`jis-2025-25.5.7-thm-20`).
