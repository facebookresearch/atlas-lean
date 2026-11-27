# Weak regularity lemma (Frieze–Kannan)

Let $V$ be a finite set and $w$ a real weight on the unordered pairs of elements of $V$ (a weighted graph with unit node weights). For every $\varepsilon > 0$ there is a partition $\mathcal P$ of $V$ into at most $4^{1/\varepsilon^2}$ classes such that

$$d_\square(w, w_{\mathcal P}) = \lVert w - w_{\mathcal P}\rVert_\square \le \varepsilon\, \lVert w\rVert_2,$$

where $w_{\mathcal P}$ is the [partition average](partition-average.md), $\lVert\cdot\rVert_\square$ the [cut norm](cut-norm.md) and $\lVert w\rVert_2 = \big(\lvert V\rvert^{-2} \sum_{x, y} w(x, y)^2\big)^{1/2}$ the [$L^2$ norm](kernel-l2-norm.md) (both norms being $0$ when $V$ is empty). Compared with Szemerédi's regularity lemma, the number of classes is only exponential in $1/\varepsilon^2$ instead of a tower, at the price of approximating $w$ only in the cut norm. The standard proof is an energy increment: while $d_\square(w, w_{\mathcal P}) > \varepsilon \lVert w\rVert_2$, refining $\mathcal P$ by the two sets witnessing it raises $\lVert w_{\mathcal P}\rVert_2^2$ by at least $\varepsilon^2 \lVert w\rVert_2^2$.

Szemerédi's regularity lemma gives the strong form for simple graphs, an $\varepsilon$-uniform equipartition with a tower-type bound on the number of parts, by the same energy-increment method; this weak form, with its exponential bound and for weighted graphs, is not a special case of it.

## Background

- [Partition average of a weighted graph](partition-average.md) and [L² norm of a weighted graph](kernel-l2-norm.md): the two quantities in the statement.
- [Cut norm](cut-norm.md): the distance in which the approximation holds.

## Sources

- C. Borgs, J. T. Chayes, L. Lovász, V. T. Sós and K. Vesztergombi, "Convergent sequences of dense graphs I: Subgraph frequencies, metric properties and testing", *Adv. Math.* 219 (2008), 1801–1851, arXiv:math/0702004, Lemma 2.4, inequality (2.10).
- A. Frieze and R. Kannan, "Quick approximation to matrices and applications", *Combinatorica* 19 (1999), 175–220.
