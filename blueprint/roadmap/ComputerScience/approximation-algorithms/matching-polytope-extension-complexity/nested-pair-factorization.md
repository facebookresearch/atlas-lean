# Nonnegative factorizations of nested-pair slack matrices and sandwiched extensions

Let $P \subseteq Q$ be presented as in the definition of the slack matrix $S=S(P,Q)$.

(i) If $S=UV$ with $U \in \mathbb{R}_{\ge 0}^{f \times r}$ and $V \in \mathbb{R}_{\ge 0}^{r \times N}$, then $K=\{x : \exists y \in \mathbb{R}_{\ge 0}^{r},\ Ax+Uy=b\}$ satisfies $P \subseteq K \subseteq Q$ and $\mathrm{xc}(K) \le r$: its extension has the $r$ inequalities $y \ge 0$, and the $f$ equations $Ax+Uy=b$ are not counted.

(ii) Conversely, if $P \subseteq K \subseteq Q$ for a polyhedron $K$ with $\mathrm{xc}(K) \le r$, then $\mathrm{rk}_+(S) \le r+1$.

In particular, for $Q=P$ (with $S$ the slack matrix of $P$) one recovers Yannakakis' identity $\mathrm{xc}(P)=\mathrm{rk}_+(S)$ up to the additive $1$.

## Proof sketch

For (i), each vertex $v_j$ lifts to $(v_j,V^{j})$, and any $x$ violating a row $A_ix \le b_i$ cannot be completed since $U_iy \ge 0$. For (ii), fix a lift $(v_j,y_j)$ in a size-$r$ extension of $K$ and let its slack vector be the column; each inequality $A_ix \le b_i$ is valid on $K$, so by LP duality it is a conic combination of the extension's inequality rows, plus a linear combination of its equations, plus a nonnegative constant $\beta_i$. The equations vanish at the lift $(v_j,y_j)$, giving $S_{ij}=\langle u_i,s_j\rangle+\beta_i$, a nonnegative factorization of inner dimension $r+1$.

## Depends on

- [Slack matrix of a nested pair of polytopes](slack-matrix-nested-pair.md)
- [Linear extensions of a polytope and their inequality count](linear-extension-size.md)
- [Nonnegative rank of a matrix](../../machine-learning/unsupervised-learning/non-negative-matrix-factorization/nonneg-rank.md)

## Proof depends on

- [A nonnegative factorization bounds the nonnegative rank](../../machine-learning/unsupervised-learning/non-negative-matrix-factorization/nonneg-rank-le-of-mul-eq.md)
- [Strong linear programming duality](../../../Geometry/convex-geometry/linear-programming/strong-linear-programming-duality.md)

## Sources

- Gabor Braun, Samuel Fiorini, Sebastian Pokutta, David Steurer, "Approximation Limits of Linear Programs (Beyond Hierarchies)", FOCS (2012), arXiv:1204.0957.
- Mihalis Yannakakis, "Expressing Combinatorial Optimization Problems by Linear Programs", Journal of Computer and System Sciences (1991).
