# Antichain size is homomesic under type-A rowmotion

Let $n$ be a natural number and let $P$
be a finite partially ordered set that is a type-A root poset of rank $n$: there is a bijection
$a \mapsto (i_a, j_a)$ from $P$ onto the set of pairs $(i, j)$ of integers with $0 \le i \le j < n$
such that $a \le b$ holds exactly when $[i_a, j_a] \subseteq [i_b, j_b]$, that is, $i_b \le i_a$
and $j_a \le j_b$. Let $\rho$ be a bijection of the set of finite antichains of $P$ such that,
for every antichain $A$, $\rho(A)$ is the set of minimal elements of the complement of the
down-set of $A$. Then the set of finite antichains of $P$ is finite, $\rho$ is bijective, and for
every antichain $A$ and every $k > 0$ with $\rho^k(A) = A$,

$$\frac{1}{k} \sum_{i=0}^{k-1} |\rho^i(A)| = \frac{n}{2}.$$

This is the type-A case of Panyushev's conjecture on antichain orbits in root posets, which
Armstrong, Stump, and Thomas proved for all crystallographic root systems.

## Sources

- D. Armstrong, C. Stump, and H. Thomas, A uniform bijection between nonnesting and noncrossing partitions, Transactions of the American Mathematical Society 365 (2013). Moved from `OpenConjectures/Combinatorics/RootPosetRowmotionHomomesy`.
