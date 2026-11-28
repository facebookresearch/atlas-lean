# Fiorini's hyperplane separation lower bound on nonnegative rank

Let $S \in \mathbb{R}_{\ge 0}^{f \times N}$ be nonzero and let $W \in \mathbb{R}^{f \times N}$ be arbitrary, with Frobenius pairing $\langle W,S\rangle=\sum_{i,j}W_{ij}S_{ij}$. Let

$$
\alpha=\max\{\langle W,\mathbf{1}_{\mathcal{R}}\rangle : \mathcal{R}=I \times J,\ I \subseteq [f],\ J \subseteq [N]\}
$$

be the largest value of $W$ on a combinatorial rectangle, and assume $\alpha > 0$. Then

$$
\mathrm{rk}_+(S) \ge \frac{\langle W,S\rangle}{\|S\|_\infty\cdot\alpha}.
$$

Combined with the factorization lemma, the same quantity minus $1$ lower-bounds $\mathrm{xc}(K)$ (extension complexity over $\mathbb{R}$) for every polytope $K$ with $P \subseteq K \subseteq Q$ whenever $S$ is a submatrix of the slack matrix $S(P,Q)$, in particular for $K = P$ when $S$ is a submatrix of a slack matrix of $P$, since deleting rows and columns does not increase nonnegative rank.

## Proof sketch

Write $S=\sum_{t=1}^{r}R_t$ with nonnegative rank-one $R_t$, so $\|R_t\|_\infty \le \|S\|_\infty$. The maximum of the bilinear form $\langle W,xy^{\top}\rangle$ over $x \in [0,1]^f$, $y \in [0,1]^N$ is attained at $0/1$ vectors, so $\langle W,R_t/\|R_t\|_\infty\rangle \le \alpha$. Summing gives $\langle W,S\rangle \le \alpha\,r\,\|S\|_\infty$.

## Depends on

- [Nonnegative rank of a matrix](../../../machine-learning/unsupervised-learning/non-negative-matrix-factorization/nonneg-rank.md)
- [Extended formulations and extension complexity](../extended-formulation.md)
- [Slack matrix of a nested pair of polytopes](slack-matrix-nested-pair.md)

## Proof depends on

- [A nonnegative factorization bounds the nonnegative rank](../../../machine-learning/unsupervised-learning/non-negative-matrix-factorization/nonneg-rank-le-of-mul-eq.md)
- [Nonnegative factorizations of nested-pair slack matrices and sandwiched extensions](nested-pair-factorization.md)

## Sources

- Thomas Rothvoss, "The Matching Polytope has Exponential Extension Complexity", STOC (2014) and Journal of the ACM (2017), arXiv:1311.2369.
