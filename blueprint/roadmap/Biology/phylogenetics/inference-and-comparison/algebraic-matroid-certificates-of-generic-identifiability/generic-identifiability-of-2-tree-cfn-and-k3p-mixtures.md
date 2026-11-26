# Generic identifiability of 2-tree CFN and K3P mixtures

**Group-based models.** For a finite abelian group $G$ of order $\kappa$ and a rooted binary tree $T$, a group-based model has edge transition matrices $M^e_{g,h}=f_e(g-h)$; in Fourier coordinates its parametrization is monomial, $q_{g_1,\dots,g_n}=\prod_e a^e_{\sum_{i\in A_e}g_i}$ when $\sum_ig_i=0$ (and $0$ otherwise), where $A_e$ is one side of the split of $e$. The Cavender–Farris–Neyman (CFN) model is $G=\mathbb Z/2$ and the Kimura 3-parameter (K3P) model is $G=\mathbb Z/2\times\mathbb Z/2$. Let $V_T$ be the Zariski closure of the model on $T$.

**Mixtures.** The 2-tree mixture model on $\{T_1,T_2\}$ is the set of distributions $\pi p_1+(1-\pi)p_2$ with $p_i$ in the model on $T_i$; its closure is the join variety $V_{T_1}\ast V_{T_2}$. The tree parameters are *generically identifiable* if for every two distinct multisets $\{T_1,T_2\}\ne\{S_1,S_2\}$ of $n$-leaf trees

$$\dim\big((V_{T_1}\ast V_{T_2})\cap(V_{S_1}\ast V_{S_2})\big)<\min\big(\dim V_{T_1}\ast V_{T_2},\ \dim V_{S_1}\ast V_{S_2}\big).$$

**Theorem.**
1. The tree parameters of the 2-tree CFN mixture model are generically identifiable for trees with at least $6$ leaves.
2. The tree parameters of the 2-tree K3P mixture model are generically identifiable for trees with at least $4$ leaves.

## Depends on

- [Coordinate projection matroid certificate of generic identifiability](coordinate-projection-matroid-certificate-of-generic-identifiability.md)

## Expansion

By the six-to-infinity theorem of Matsen, Mossel and Steel, identifiability of 2-tree mixtures on six leaves propagates to all $n\ge6$, so the CFN case reduces to $22{,}773$ pairs of multisets of 6-leaf trees up to symmetry. All CFN join varieties there have the expected dimension $\dim V_{T_1}+\dim V_{T_2}+1=19$, and for all but one pair a coordinate set independent on one join and dependent on the other is found from Jacobians; the last pair, whose matroids are conjectured to coincide, is separated by invariants from a Gröbner basis computed up to degree four. For K3P with $n\ge6$, projecting onto the Fourier coordinates indexed by a subgroup $G\cong\mathbb Z/2$ of $\mathbb Z/2\times\mathbb Z/2$ maps each K3P tree variety onto the CFN one, and linear projections commute with joins, so distinct CFN joins force distinct K3P joins. The 4-leaf K3P cases are certified directly by the matroid algorithm, and the 5-leaf case follows because two distinct multisets of 5-leaf trees remain distinct after restriction to some four leaves.

## Sources

- B. Hollering, S. Sullivant, "Identifiability in phylogenetics using algebraic matroids", arXiv:1909.13754 (2019), <https://doi.org/10.48550/arXiv.1909.13754>. Section 4 (Definitions 4.2, 4.4; Theorem 4.5; Theorems 4.6, 4.7; Conjecture 4.8).
