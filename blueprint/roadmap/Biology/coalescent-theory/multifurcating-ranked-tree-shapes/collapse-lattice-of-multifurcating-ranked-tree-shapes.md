# Collapse lattice of multifurcating ranked tree shapes

**Setting.** Let $\mathcal{MT}_N$ be the set of multifurcating ranked tree shapes with $N$ tips (internal nodes totally ordered by rank, each with at least two children). An internal edge $(e,e+1)$ joins two internal nodes of consecutive ranks. *Collapsing* it merges the two nodes into one multifurcation, giving a shape with one fewer internal node. Write $T\le T'$ if $T'$ is obtained from $T$ by a sequence of collapses, and adjoin a minimum element $\emptyset$ covered by the binary shapes; the star tree $(N)$ is the maximum.

**F-matrix encoding (Theorem 9, Theorem 11).** $\mathcal{T}_{N,K}$ is in bijection with $K\times K$ lower-triangular nonnegative integer matrices $F$ whose diagonal strictly increases to $F_{K,K}=N$ with subdiagonal $F_{i+1,i}=F_{i,i}-1$, plus column constraints, where $F_{i,j}$ counts lineages present in the $j$-th inter-event interval that do not split before the $i$-th. Collapsing edge $(e,e+1)$ corresponds to deleting row and column $e$ of $F$.

**Theorem 15.** $(\mathcal{MT}_N\cup\{\emptyset\},\le)$ is a lattice.

**Theorem 16 (degrees).** For $T_{N,K}$ with F-matrix $F$, the number of shapes obtainable by one collapse is

$$\deg^+(T_{N,K})=1+\sum_{e=2}^{K}\mathbf 1\big(F_{e,1:e-1}=F_{e+1,1:e-1}\big),$$

and the number of shapes that collapse onto it in one step is $\deg^-(T_{N,K})=\sum_{i=1}^K\big((l_i+1)2^{k_i}-k_i-3+\mathbf 1(l_i=0)\big)$, where node $i$ has $l_i$ leaf children and $k_i$ internal children.

**Theorem 17.** The maximum backward degree in $\mathcal{MT}_N$ is attained by the shape $\ddot T_N$ with $\lfloor (N-2)/2\rfloor+1$ internal nodes: a root carrying $\lfloor (N-2)/2\rfloor$ cherries and $2+(N\bmod 2)$ leaves. Its backward degree is $(3+(N\bmod2))\,2^{\lfloor N/2\rfloor}-\lfloor N/2\rfloor-3$, and it also maximizes the total degree (Theorem 18).

## Depends on

- [Enumeration of multifurcating ranked tree shapes](enumeration-of-multifurcating-ranked-tree-shapes.md)

## Expansion

The lattice property is checked with Björner's criterion (Theorem 8): a bounded poset of finite rank in which any two elements covering a common element have a least upper bound is a lattice. If $T_X$ and $T_Y$ arise from $T_Z$ by collapsing edges $e_X<e_Y$, collapsing both edges of $T_Z$ (deleting rows and columns $e_X$ and $e_Y$ from $F(T_Z)$) gives their join; for two binary shapes, which cover only $\emptyset$, an explicit algorithm on F-matrices builds the join (Proposition 14). The degree formulas count admissible deletions (rows $e$ that still yield a valid F-matrix) and the ways to split a node with $k$ internal and $l$ leaf children into two consecutive nodes. The maximal degree and the lattice diameter feed bottleneck and relaxation-time bounds on the mixing time of random walks on the Hasse diagram (Theorems 19–22, from Levin–Peres).

## Sources

- J. Zhang, N. A. Rosenberg, J. A. Palacios, "The space of multifurcating ranked tree shapes: enumeration, lattice structure, and Markov chains", arXiv preprint (2025), Theorems 8, 9, 11, 15–22 and Proposition 14, <https://doi.org/10.48550/arXiv.2506.10856>.
