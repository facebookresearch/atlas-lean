# Branch-length polynomial is a complete invariant of branching trees

**Definition.** Let $B$ be a rooted tree with positive branch lengths. Define $P(v,x,y)=x$ at each leaf $v$, and at an internal vertex $v$ with children $v_1,\dots,v_k$ joined by edges of lengths $w_1,\dots,w_k$,

$$P(v,x,y)=\prod_{i=1}^k\big(w_iy+P(v_i,x,y)\big).$$

$P(B,x,y)$ is the polynomial at the root. For unlabeled rooted trees $T$ (all $w_i=1$), $P(T,x,y)=L(T,x+y,y)-y$, where $L$ is the tree-distinguishing polynomial of Liu. Two trees with branch lengths are *isomorphic* if their underlying unlabeled rooted trees are isomorphic by a map preserving every branch length. A *branching tree* is a rooted tree with branch lengths having no vertex of degree two other than possibly the root; it is *proper* if the root has degree greater than one.

**Theorem 1.** Two unlabeled rooted trees $T_1,T_2$ are isomorphic if and only if $P(T_1,x,y)=P(T_2,x,y)$.

**Theorem 2.** Isomorphic trees with branch lengths have identical polynomials.

**Theorem 3 (principal-subtree expansion).** A principal subtree $S$ of $B$ (one containing the root) is obtained by pruning a set of pairwise incomparable edges $e_1,\dots,e_\beta$. Assign it the monomial $q(S)=w\,x^\alpha y^\beta$, where $\alpha$ is the number of leaves of $B$ kept in $S$ and $w$ is the product of the lengths of $e_1,\dots,e_\beta$. Then

$$P(B,x,y)=\sum_{S\in\mathcal S(B)}q(S).$$

**Theorem 4.** Two branching trees $B_1,B_2$ are isomorphic if and only if $P(B_1,x,y)=P(B_2,x,y)$.

## Expansion

Theorem 3 is the expansion of the recursive product: at each child edge one either keeps the edge and recurses into the child (term $P(v_i,x,y)$) or prunes it with everything below (term $w_iy$), and leaves contribute $x$. Theorem 4 is proved by induction on the number of leaves for proper branching trees: the polynomial of a proper tree factors as a product of factors $w_iy+P(B_i)$, one per root child, and unique factorization in $\mathbb R[x,y]$ together with the induction hypothesis recovers each child subtree and its edge length. The theorem is stated for trees without elementary (non-root degree-two) vertices, the class that contains standard phylogenetic trees; the induction also handles a root of degree one by peeling off its single edge. The encoding gives an exact, alignment-free representation of phylogenies with branch lengths for computing distances.

## Sources

- P. Liu, J. C. Pons, G. Ribas, "Polynomial encoding of rooted trees with branch lengths", arXiv preprint (2026), Theorems 1–4, <https://doi.org/10.48550/arXiv.2607.06591>.
