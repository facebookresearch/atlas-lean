# Tree topologies along tropical line segments in ultrametric space

**Setting.** An equidistant (ultrametric) phylogenetic tree on $n$ leaves is represented by its vector of pairwise distances $u \in \mathbb R^{e}$, $e = \binom n2$, satisfying the ultrametric condition $\max\{u_{ij},u_{ik},u_{jk}\}$ attained at least twice. Working in the tropical projective torus $\mathbb R^e/\mathbb R\mathbf 1$ (max-plus arithmetic $a\oplus b = \max\{a,b\}$, $a\odot b = a+b$), the space of ultrametrics $\mathcal U_n$ is the tropicalization of a linear space and is tropically convex. The *tropical line segment* between $u$ and $v$ is

$$\Gamma_{u,v} = \{a_1\odot u \oplus a_2\odot v : a_1,a_2 \in \mathbb R\},$$

a concatenation of at most $e-1$ ordinary line segments; it is unique, a geodesic in $\mathcal U_n$ for the tropical metric, and intrinsic to $\mathcal U_n$. It can be computed in $O(n^2\log n)$ time.

**Topology along a segment.** Points on the same ordinary piece of $\Gamma_{u,v}$ have the same tree topology (more generally, two points in the same cell of a tropical polytope spanned by ultrametrics have the same topology).

**Theorem (clades are preserved).** If a leaf set $X_0$ forms a clade in both equidistant trees $T_1$ and $T_2$, with the same subtree topology, then $X_0$ is a clade with that same topology in every tree on $\Gamma_{T_1,T_2}$.

**Theorem (one NNI apart).** If the topologies of $T_1$ and $T_2$ differ by one nearest-neighbour interchange, every tree on $\Gamma_{T_1,T_2}$ has the topology of $T_1$ or of $T_2$, possibly with zero-length branches.

**Theorem (segments to the star tree).** For an equidistant tree $T$ with distinct speciation times $t_1,\dots,t_k$ ($k \le n-1$), the tropical segment from $T$ to the star tree (the origin of $\mathbb R^e/\mathbb R\mathbf 1$) is the concatenation of segments between the ultrametrics of the trees $T^i, T^{i+1}$ obtained by successively collapsing $T$ at its speciation times.

**Theorem (generic segments avoid the star tree).** For $x,y$ drawn independently and uniformly from equidistant trees of fixed height, $\Gamma_{x,y}$ passes through the star tree with probability zero when $n \ge 5$.

## Expansion

A point of $\Gamma_{u,v}$ is the coordinatewise maximum of two translated vectors, $\max\{u + a_1, v + a_2\}$, so as $a_1 - a_2$ varies each coordinate switches from $u$ to $v$ at a breakpoint; between breakpoints the point moves linearly and the order of the pairwise distances, hence the topology, is fixed. Clade preservation and the NNI statement are proved by tracking, coordinate by coordinate, which of the two endpoints realizes the maximum on each piece of the segment, and checking the ultrametric three-point conditions for the leaves in $X_0$ (resp. the four subtrees involved in the NNI).

## Sources

- Ruriko Yoshida and Shelby Cox, "Tree Topologies along a Tropical Line Segment", arXiv:2104.09022 (2021), Theorem 1 (ultrametrics as a tropical linear space, quoted), Proposition 2, Theorem 3 (quoted), Proposition 4, Theorem 5, Proposition 6, Theorems 7, 8 and 9, <https://doi.org/10.48550/arXiv.2104.09022>.
