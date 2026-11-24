# The margin costs of voting classifiers are no more complex than the base classifiers

Let $B \subseteq \mathbb{R}^n$ be nonempty and bounded (the value vectors of the base classifiers on a sample), let $y \in \mathbb{R}^n$ with $|y_i| \le 1$ (labels $\pm 1$), and let $\varphi$ be $L$-Lipschitz. Then, with $R$ the [empirical Rademacher complexity](rademacher-complexity.md),

$$R\big(\{(\varphi(y_i a_i))_i : a \in \operatorname{conv} B\}\big) \le L\, R(B).$$

A voting classifier $f = \sum_h a_h h$ with $a_h \ge 0$ and $\sum_h a_h = 1$ has its value vector in $\operatorname{conv} B$, so the left side is the complexity of the [margin costs](margin-costs.md) of all voting classifiers, however many base classifiers they combine. The bound combines [convex hull invariance](rademacher-complexity-convex-hull.md) with [the contraction lemma](rademacher-complexity-coord-map-le.md) applied to the coordinate maps $x \mapsto \varphi(y_i x)$, which are $L$-Lipschitz because $|y_i| \le 1$.

## Background

- [The Rademacher risk bound](risk-le-empirical-add-rademacher.md): with a cost of this form, the risk bound becomes a margin bound for voting classifiers, Bartlett and Mendelson's Theorem 7.
- [AdaBoost's training margins](../../online-learning-and-boosting/adaboost/margin-err-le.md): the empirical side of the margins explanation of boosting.

## Sources

- P. L. Bartlett and S. Mendelson, "Rademacher and Gaussian complexities: risk bounds and structural results", *J. Mach. Learn. Res.* 3 (2002), 463–482, <https://jmlr.csail.mit.edu/papers/volume3/bartlett02a/bartlett02a.pdf>, Theorem 12, parts 2 (convex hulls) and 4 (Lipschitz composition), of which the two ingredients are the analogues in the convention used here; the result bounds the complexity term $2 L R_n(F)$ of their Theorem 7 when $F$ is a convex hull.
- R. E. Schapire, Y. Freund, P. Bartlett and W. S. Lee, "Boosting the margin: a new explanation for the effectiveness of voting methods", *Ann. Statist.* 26 (1998), 1651–1686, Section 2 (the convex hull $\mathcal{C}$ of the base classifiers and the margin $y f(x)$).
