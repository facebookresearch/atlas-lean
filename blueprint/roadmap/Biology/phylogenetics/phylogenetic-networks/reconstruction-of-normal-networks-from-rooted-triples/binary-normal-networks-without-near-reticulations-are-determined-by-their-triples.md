# Binary normal networks without near reticulations are determined by their triples

**Definitions.** A rooted binary phylogenetic network $N$ on $X$ is normal if it is tree-child (every non-leaf vertex has a child that is a tree vertex or a leaf) and has no shortcuts (no reticulation edge $(u,v)$ with another directed path from $u$ to $v$). $R(N)$ is the set of rooted binary triples on three leaves displayed by $N$, and $Q(N)$ the set of rooted four-leaf trees displayed by $N$. Reticulations $u,v$ are near-sibling if some tree vertex has two children, one of them $v$ and the other a tree vertex that is a parent of $u$; they are near-stack if the unique child of $u$ is a tree vertex that is a parent of $v$. $N$ has no near reticulations if it has neither.

**Theorem.**

- (Trees) For rooted binary phylogenetic trees, $R(T_1)=R(T_2)$ iff $T_1\cong T_2$.
- (Triples and quartets) For binary normal networks, $R(N_1)=R(N_2)$ and $Q(N_1)=Q(N_2)$ iff $N_1\cong N_2$.
- (Triples alone) For binary normal networks with no near reticulations, $R(N_1)=R(N_2)$ iff $N_1\cong N_2$.

Binary level-1 normal networks have no near reticulations, so they are determined by their triples. Excluding near-sibling reticulations is necessary: if $N$ is normal with a pair of near-sibling reticulations then, apart from a structural exception, there is a non-isomorphic normal network $N'$ with $R(N')=R(N)$. Whether excluding near-stack reticulations is necessary is open.

## Expansion

Every tree-child network with at least two leaves has a cherry or a reticulated cherry $\{a,b\}$ (the parent of $b$ is a reticulation and the parent of $a$ is a parent of that reticulation). The proof is by induction on $|X|$: the rooted triples containing $a$ and $b$, together with the grandparent of $b$ not adjacent to $a$, identify the reticulated cherry in both networks, and reducing it gives smaller normal networks with equal triple sets. Near-sibling reticulations are exactly where three-leaf subtrees fail to locate the second parent of a reticulation, which four-leaf caterpillars resolve.

## Sources

- A. Francis, C. Semple, "Binary normal networks without near reticulations can be reconstructed from their rooted triples", *Journal of Mathematical Biology* 93(6) (2026), 69, Theorems 1.1, 1.2 and 1.3 and the definitions preceding Theorem 1.3, <https://doi.org/10.1007/s00285-026-02483-2> (preprint arXiv:2512.12969).
