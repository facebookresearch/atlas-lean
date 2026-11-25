# Single linkage gives the maximal subdominant ultrametric

Let $d$ be a dissimilarity on a set $X$, and let $u : X \times X \to \mathbb{R}$ be symmetric,
zero on the diagonal, satisfy the ultrametric inequality $u(x, z) \le \max(u(x, y), u(y, z))$ and
$u \le d$. Then $u \le u^*$, where $u^*$ is the [single-linkage ultrametric](sl-dist.md) of $d$
(Carlsson and Mémoli, JMLR 11 (2010), Example 7, the remark after equation (4)). Together with
[$u^* \le d$](sl-dist-le.md) and [the ultrametric inequality for $u^*$](sl-dist-le-max.md),
$u^*$ is the largest pseudo-ultrametric below $d$ when $d \ge 0$, and the largest ultrametric below $d$ when
$d$ is a metric on a finite set.
