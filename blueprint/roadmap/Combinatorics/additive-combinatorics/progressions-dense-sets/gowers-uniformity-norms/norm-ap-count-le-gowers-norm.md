# Generalized von Neumann theorem

Let $G$ be a finite abelian group, let $\mathbb{E}$ denote an average over $G$, let  $k \ge 2$, let $|G|$ be coprime to $(k-1)!$ and let $f_0, \dots, f_{k-1} : G \to \mathbb{C}$ take values in the closed unit disc. Then for every $j < k$,

$$|\Lambda_k(f_0, \dots, f_{k-1})| = \Bigl|\mathbb{E}_{x, r} \prod_{i < k} f_i(x + i r)\Bigr| \le \|f_j\|_{U^{k-1}}.$$

This is Proposition 1.7 of Green and Tao; Gowers's Theorem 3.2 is the case $G = \mathbb{Z}_N$ with the bound through the last function. Counting $k$-term progressions is therefore controlled by the $U^{k-1}$ norm: a set whose balanced function has small $U^{k-1}$ norm contains about as many progressions as a random set of the same density, which is how Gowers's proof of Szemerédi's theorem reduces to an inverse theorem for $U^{k-1}$. The restriction $k \ge 2$ avoids the degenerate $U^0$.

## Informally uses

- [Generalized von Neumann theorem, general form](norm-expect-prod-le-gowers-norm.md): the case $a_i = i$; the differences $i - j$ divide $(k - 1)!$.

## Background

- [Counting lemma](../../../../GraphTheory/random-graphs/graph-limits/abs-hom-density-sub-hom-density-le.md): the graph analogue, in which subgraph counts are controlled by the cut norm, as progression counts are controlled by $U^{k-1}$ here.

## Sources

- B. Green and T. Tao, "An inverse theorem for the Gowers $U^3(G)$ norm", Proc. Edinb. Math. Soc. 51 (2008), 73–153; numbering of arXiv:math/0503014, Proposition 1.7.
- William Timothy Gowers, "A new proof of Szemerédi's theorem", Geom. Funct. Anal. 11 (2001), 465–588, Theorem 3.2 and Corollary 3.3.
