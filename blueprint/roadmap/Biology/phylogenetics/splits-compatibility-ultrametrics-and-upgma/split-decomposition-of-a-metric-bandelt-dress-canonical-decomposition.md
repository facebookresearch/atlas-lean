# Canonical split decomposition of a metric

Let $X$ be a finite set and call a metric on $X$ any symmetric $d : X \times X \to \mathbb{R}_{\ge 0}$ vanishing on the diagonal and satisfying the triangle inequality, with $d(x, y) = 0$ allowed for $x \ne y$. A decomposition $d = d_1 + \dots + d_k$ into metrics is coherent if for every map $f : X \to \mathbb{R}$ with $f(x) + f(y) \ge d(x, y)$ for all $x, y$ there are maps $f_1, \dots, f_k$ with $f_i(x) + f_i(y) \ge d_i(x, y)$ for all $x, y$ and all $i$, the $f_i$ summing to $f$. (Dress, Huber and Moulton print the condition without the last requirement; without it every decomposition into metrics would be coherent, since $f_i = f$ always works because $d_i \le d$.) A metric $d$ is a split metric if the zero-distance relation $x \simeq y \Leftrightarrow d(x, y) = 0$ has exactly two equivalence classes, and split-prime if it is not a coherent sum of a split metric and another metric. Dress, Huber and Moulton (2001, Section 4) record the theorem of Bandelt and Dress: every metric $d$ on $X$ has a unique coherent decomposition $d = d_1 + \dots + d_k + d_0$, the canonical split decomposition, into pairwise linearly independent split metrics $d_1, \dots, d_k$ and a split-prime metric $d_0$ (possibly $0$); the $d_i$ are linearly independent, and so are $d_1, \dots, d_k, d_0$ when $d_0 \ne 0$; up to scaling, $d_1, \dots, d_k$ are exactly the split metrics $d'$ for which $d - d'$ is a metric and $d', d - d'$ form a coherent decomposition of $d$; and for a tree-like metric $d_0 = 0$ and the $d_i$ correspond one-to-one to the edges of the associated tree. In particular at most $\binom{n}{2}$ split metrics, up to scaling, occur, for $|X| = n$.

## Depends on

- [Split decomposition of a tree metric](../../../Biology/phylogenetics/neighbor-joining/dist-eq-sum-darts.md)

## Expansion

1. Definitions: metrics in the above sense, coherent decompositions, split metrics and split-prime metrics, with the precise form of the coherence condition as in Bandelt and Dress.
2. Isolation indices of splits, and the split metrics that occur with positive coefficient.
3. Existence and uniqueness of the canonical decomposition, and linear independence of its summands.
4. The characterization of the occurring split metrics up to scaling, and the bound $\binom{n}{2}$ from linear independence.
5. Tree-like metrics as the case $d_0 = 0$, with the split metrics of the edges, given by the split decomposition of a tree metric.

## Sources

- A. Dress, K. T. Huber and V. Moulton, Metric spaces in pure and applied mathematics, Doc. Math. Extra Volume Quadratic Forms LSU (2001), 121–139, Section 4. <https://doi.org/10.4171/dms/2/5>
- Original result: H.-J. Bandelt and A. W. M. Dress, A canonical decomposition theory for metrics on a finite set, Adv. Math. 92 (1992), 47–105. <https://doi.org/10.1016/0001-8708(92)90061-O> The decomposition theorem follows Dress, Huber and Moulton, Section 4.
