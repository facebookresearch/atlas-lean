# Zero pattern of the inverse of a layered mixed matrix

**Definition.** A square matrix $L$ over $\mathbb K(t_{ij})$ is a layered mixed matrix (LM-matrix) if after a column permutation $L=[\,T\mid Q\,]$, where $Q$ has entries in the field $\mathbb K$ and each entry of $T$ is either $0$ or a distinct indeterminate $t_{ij}$, all indeterminates being algebraically independent over $\mathbb K$.

**Combinatorial canonical form (Murota).** A nonsingular LM-matrix is LM-equivalent (row and column permutations plus a change of basis of the numeric part) to a unique finest block upper-triangular LM-matrix $\bar L$ with row/column partition $[n]=M_1\sqcup\dots\sqcup M_p$ whose diagonal blocks are LM-irreducible. The blocks carry a partial order $\preceq$; its Hasse diagram is the CCF directed graph, in which there is a directed path from $M_a$ to $M_b$ iff $M_a\preceq M_b$.

**Theorem (Murota).** If $L$ is LM-irreducible then every entry of $L^{-1}$ is nonzero; and if $L$ has a nonempty symbolic part, $\det L$ is an irreducible polynomial iff $L$ is essentially LM-irreducible.

**Theorem (inverse of a CCF).** If $\bar L$ is a nonsingular LM-matrix in CCF with blocks $M_1,\dots,M_p$, then for all $a,b$:

$$\bar L^{-1}[M_a,M_b]\ \text{is fully dense if } M_a\preceq M_b,\qquad \bar L^{-1}[M_a,M_b]=\mathbf 0\ \text{otherwise}.$$

So the zero pattern of $\bar L^{-1}$ is read off from reachability in the CCF directed graph.

**Linearly transformed generic matrices.** If $T$ is $n\times m$ sparse generic, $S\in\mathbb K^{m\times n}$ has rank $m\le n$ and $Q$ is a Gale dual of $S$ (columns spanning $\ker S$), then $\det(ST)=c\,\det[\,T\mid Q\,]$ for a constant $c\ne0$, so $\det(ST)$ factors exactly as the LM-matrix $[T\mid Q]$ does.

## Expansion

Block upper-triangularity gives $\bar L^{-1}[M_a,M_b]=\mathbf 0$ when $a>b$, and the block-triangular inverse formula expresses $\bar L^{-1}[M_a,M_b]$ as a sum over chains of blocks from $a$ to $b$, which vanishes when $M_a,M_b$ are incomparable. When $M_a\preceq M_b$, each diagonal block's inverse is fully dense by Murota's theorem, and algebraic independence of the indeterminates rules out cancellation along a covering chain, so every entry is a nonzero rational function. The determinant identity follows by multiplying $[T\mid Q]$ on the left by an invertible matrix whose first rows are $S$.

## Sources

- A. Kuhrs, M. L. Telek, N. Vassena, "Layered mixed matrices and reaction networks", arXiv:2609.05100 (2026), Section 2 (Definition of LM-matrix, Theorem 2.7, Theorems 2.11–2.13, Proposition 2.22), <https://doi.org/10.48550/arXiv.2609.05100>.
