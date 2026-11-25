# Smith's counterexample to Erdős Problem 1198

There is a colouring
$c : \mathbb{N} \to \{0, 1\}$ such that for every strictly increasing sequence
$0 < a_0 < a_1 < \cdots$ of natural numbers, the numbers $\sum_{j < k} \prod_{i \in S_j} a_i$,
taken over all $k \ge 1$ and all pairwise disjoint nonempty finite sets
$S_0, \dots, S_{k-1} \subseteq \mathbb{N}$ other than those with $k = 1$ and $|S_0| = 1$, do not
all have the same colour.

Smith (SIAM J. Discrete Math. 2001) constructed, for $m \ne n$, a two-cell partition of
$\mathbb{N}$ in which no cell contains $SP_n(x) \cup SP_m(y)$ for any sequences $x$ and $y$, where
$SP_m(x)$ is the set of sums $\prod_{t \in F_1} x_t + \cdots + \prod_{t \in F_m} x_t$ over nonempty
finite sets $F_1 < \cdots < F_m$ (here $F < F'$ means that every element of $F$ is less than every
element of $F'$). Taking $x = y = a$, $m = 2$ and $n = 3$, every such sum is one of the numbers
above, so they cannot all have one colour. Hindman's theorem is the case where every $S_j$ is a
singleton.

## Sources

- T. F. Bloom, Erdős Problems, Problem #1198, https://www.erdosproblems.com/1198 (status DISPROVED); resolution: G. L. Smith, Partitions and (m and n) sums of products, J. Combin. Theory Ser. A 72 (1995), 77-94; G. L. Smith, Partitions and (m and n) sums of products - two cell partition, SIAM J. Discrete Math. 14 (2001), 356-369, erdosproblems.com/1198: a counterexample was provided by Smith [Sm95]; the two-colour counterexample is the 2001 paper (abstract: for m ≠ n, a two cell partition of ℕ such that neither cell contains SP_n(⟨x_t⟩) ∪ SP_m(⟨y_t⟩), SP_m the sums of m increasing products), https://doi.org/10.1137/S0895480198349014.
