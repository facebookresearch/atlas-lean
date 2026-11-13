# Circular Eulerian numbers are shifted Eulerian numbers

An excedance of a permutation
$\sigma$ of $n$ objects $1, \dots, n$ is an index $i$ with $\sigma(i) > i$. Let $C_{n,m}$ be the
number of circular permutations of $n$ objects (permutations with a single cycle through all
$n \ge 1$ points) with exactly $m$ excedances, and let $A_{n,m}$ be the number of permutations of
$n$ objects with exactly $m$ excedances (the $0$-associated Stirling Eulerian number, which
counts the permutations all of whose cycle lengths exceed $0$, that is, all permutations). Then
$C_{1,0} = 1$; for all $n \ge 2$ and $1 \le m \le n$ we have $C_{n,m} = A_{n-1,m-1}$; and for
every $n \ge 2$ the polynomial identity $C_n(x) = x\,A_{n-1}(x)$ holds in $\mathbb{Z}[x]$, where
$C_n(x) = \sum_{m=0}^{n} C_{n,m} x^m$ and $A_{n-1}(x) = \sum_{m=0}^{n-1} A_{n-1,m} x^m$.

## Sources

- Imboa-Navalona Manjaka Rakotoson and Fanja Rakotondrajao, *Associated Stirling Eulerian Numbers and Their q-Analogues*, Journal of Integer Sequences 28 (2025), Article 25.5.7, Theorem 5 (`jis-2025-25.5.7-thm-5`).
