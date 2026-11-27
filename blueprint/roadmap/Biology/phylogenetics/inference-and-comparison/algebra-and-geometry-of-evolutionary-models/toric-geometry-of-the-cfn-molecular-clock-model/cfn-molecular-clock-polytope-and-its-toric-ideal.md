# The CFN molecular clock polytope and its toric ideal

**Setting.** Let $T$ be a rooted binary tree with $n \ge 2$ leaves and internal nodes $v_1,\ldots,v_{n-1}$ (the root included). The **Cavender–Farris–Neyman model with a molecular clock** (CFN-MC) is the two-state group-based model on an equidistant version of $T$. After the discrete Fourier transform, a leaf labelling $(i_1,\ldots,i_n) \in \mathbb Z_2^n$ with even sum determines a unique **path system** $\mathcal P$: edge-disjoint paths pairing up the leaves labelled 1. The **top-vector** $[\mathcal P] \in \{0,1\}^{n-1}$ marks the internal nodes that are the top-most node of some path in $\mathcal P$. The **CFN-MC ideal** $I_T$ is the kernel of the monomial map $r_{k} \mapsto \prod_{i=1}^{n-1} b^{v_i}_{k_i}$, with $k$ ranging over top-vectors, and the **CFN-MC polytope** is $R_T = \operatorname{conv}\{[\mathcal P]\}$. A **cluster** is a connected set of internal nodes each adjacent to three internal nodes, and $N(C)$ is its set of internal neighbours.

**Theorem (Theorem 1).** For every rooted binary tree $T$ with $n$ leaves:
1. $I_T$ has a Gröbner basis of homogeneous quadratic binomials with squarefree initial terms (Theorem 34); hence $R_T$ has a regular unimodular triangulation and is normal (Corollary 49).
2. $R_T$ has exactly $F_{n+1}$ vertices, where $F_1=F_2=1$ are the Fibonacci numbers, so $2$ vertices for $n=2$ and $3$ for $n=3$ (Proposition 22, which writes $F_n$ with the convention $F_0=F_1=1$).
3. The facets of $R_T$ are given by $x_i \ge 0$ for each internal node $i$, $x_i + x_j \le 1$ for adjacent internal nodes $i,j$, and

$$2\sum_{i \in C} x_i + \sum_{j \in N(C)} x_j \le |C| + 1 \quad \text{for every cluster } C$$

(Corollary 32).
4. The normalized volume of $R_T$ is the Euler zig-zag number $E_{n-1}$, the number of alternating permutations of $n-1$ letters (Theorem 51).
5. The Hilbert series of $I_T$ depends only on $n$, not on the shape of $T$ (Theorem 69).

## Expansion

Two adjacent internal nodes cannot both be top-most nodes, since the path through the upper one would have to use an edge below the lower one; this is the source of the inequalities $x_i + x_j \le 1$. Under the clock, parameters attach to internal nodes (heights) rather than to edges, which is why the polytope lives in $\mathbb R^{n-1}$. For the caterpillar $C_{n}$, an explicit unimodular affine map sends $R_{C_n}$ to the order polytope of the zig-zag poset on $n-1$ elements, so the Ehrhart function and volume come from alternating permutations (Proposition 56, Corollary 57). For general trees, a bijection between lattice points of $mR_T$ and $mR_{T'}$ for trees related by a rotation shows that the Ehrhart function is invariant, which transfers the caterpillar result to every tree. The quadratic Gröbner basis is built by gluing ideals along toric fiber products at nodes with exactly two internal neighbours.

## Sources

- Jane Ivy Coons and Seth Sullivant, "The Cavender–Farris–Neyman model with a molecular clock", arXiv:1805.04175 (2018), Theorem 1 and Definitions 12, 14, 17, 20 and 28, Proposition 22, Corollary 32, Theorem 34, Corollary 49, Theorem 51, Proposition 56, Corollary 57 and Theorem 69, <https://doi.org/10.48550/arXiv.1805.04175>. Published version: Advances in Applied Mathematics 123 (2021) 102119, <https://doi.org/10.1016/j.aam.2020.102119>.
