# Slack matrix of a nested pair of polytopes

Let $P=\mathrm{conv}\{v_1,\dots,v_N\} \subseteq \mathbb{R}^d$ and let $Q=\{x \in \mathbb{R}^d : Ax \le b\}$ with $A \in \mathbb{R}^{f \times d}$ be a polytope with $P \subseteq Q$. The slack matrix of the pair $(P,Q)$ with respect to these presentations is the nonnegative matrix

$$
S(P,Q) \in \mathbb{R}_{\ge 0}^{f \times N}, \qquad S(P,Q)_{ij}=b_i-A_iv_j .
$$

When $Q=P$ and $Ax \le b$ is an inequality description of $P$, this is the slack matrix of $P$. Its nonnegative rank $\mathrm{rk}_+(S)$ is the least $r$ with $S=UV$, $U \in \mathbb{R}_{\ge 0}^{f \times r}$, $V \in \mathbb{R}_{\ge 0}^{r \times N}$.

## Depends on

- [Nonnegative rank of a matrix](../../../machine-learning/unsupervised-learning/non-negative-matrix-factorization/nonneg-rank.md)
- [Faces of a convex polytope](../../../../Combinatorics/polytopes-simplicial-complexes/faces-of-convex-polytopes/faces.md)

## Sources

- Mihalis Yannakakis, "Expressing Combinatorial Optimization Problems by Linear Programs", Journal of Computer and System Sciences (1991).
- Gabor Braun, Samuel Fiorini, Sebastian Pokutta, David Steurer, "Approximation Limits of Linear Programs (Beyond Hierarchies)", FOCS (2012), arXiv:1204.0957.
