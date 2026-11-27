# Circular Eulerian numbers

For natural numbers $n$ and $m$, the circular Eulerian number
$C_{n,m}$ is the number of permutations $\sigma$ of $\{0, 1, \dots, n-1\}$ such that $n \ge 1$,
all points lie in a single cycle of $\sigma$ (for any two points $i$ and $j$ there is an integer
$k$ with $\sigma^k(i) = j$), and $\sigma$ has exactly $m$ excedances, that is, exactly $m$ points
$i$ with $\sigma(i) > i$. In particular $C_{0,m} = 0$ for every $m$, and the identity permutation
of a single point counts as circular.

For $n \ge 2$ the permutations with a single cycle through all points are exactly the $n$-cycles.

## Sources

- Imboa-Navalona Manjaka Rakotoson and Fanja Rakotondrajao, *Associated Stirling Eulerian Numbers and Their q-Analogues*, Journal of Integer Sequences 28 (2025), Article 25.5.7, Theorems 5 and 6 (excedance distribution `C_n(x)` over circular permutations, `C_{1,0} = 1`).
