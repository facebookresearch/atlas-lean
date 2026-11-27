# The swap complex (faces complex) of a high-dimensional expander

Let $X$ be a $d$-dimensional complex and $k \ge 1$ with $3k - 1 \le d$. The **swap complex** (or faces complex) $F^{k}X$ is the $2$-dimensional complex whose vertices are the $(k-1)$-faces of $X$, whose edges are pairs $\{s, t\}$ of disjoint $(k-1)$-faces with $s \sqcup t \in X(2k-1)$, and whose triangles are triples $\{s, t, u\}$ of pairwise disjoint faces with $s \sqcup t \sqcup u \in X(3k-1)$, weighted by the induced face distributions of $X$. For $\beta > 0$ and $r \ge 0$ with $3(r+1) - 1 \le d$, $X$ has **$(\beta, r)$-swap coboundary (cocycle) expansion** if $F^{r+1}X$, whose vertices are the $r$-faces of $X$, is a $\beta$-coboundary (cocycle) expander for $1$-cochains. Dikstein, Dinur and Lubotzky index the faces complex by the dimension of its vertex faces, so their $F^{r}X$ is $F^{r+1}X$ here, together with faces of dimension above $2$ that $1$-cochain expansion does not use (Definitions 2.16 and 2.17). Following their Definitions 2.7 and 2.8, a complex $Y$ is a $\beta$-cocycle expander for $1$-cochains if for every group $\Gamma$ and every antisymmetric $f : \vec{Y}(1) \to \Gamma$ there is a $1$-cocycle $g$ with $\beta \operatorname{dist}(f, g) \le \operatorname{wt}(\delta f)$, distances being measured by the face distributions of $Y$, and a $\beta$-coboundary expander if moreover every $1$-cocycle is a coboundary, for every $\Gamma$; with $\Gamma = \mathbb{F}_2$, $\beta$-coboundary expansion gives $h^1(Y) \ge \beta$. Their Theorem 1.3, which calls quotients of the affine symplectic building $(d, \exp(-O(\sqrt{d})))$-swap cocycle expanders, uses $r = d$ and $\beta = \exp(-O(\sqrt{d}))$. Agreement tests that compare local functions on disjoint or intersecting faces of $X$ are naturally tests on the swap complex.

## Depends on

- [Coboundary expansion of a simplicial complex](coboundary-expansion.md)

## Sources

- Y. Dikstein, I. Dinur, A. Lubotzky, "Low acceptance agreement tests via bounded-degree symplectic HDXs", FOCS (2024), arXiv:2402.01078.
- Y. Dikstein, I. Dinur, "Agreement theorems for high dimensional expanders in the small soundness regime: the role of covers", arXiv:2308.09582 (2023), ECCC TR23-119.
