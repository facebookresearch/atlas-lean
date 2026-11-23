# The complexity term of the margin bound for voting classifiers

Let $B \subseteq \mathbb{R}^n$ be nonempty and bounded, let $|y_i| \le 1$ and $\theta > 0$. Then

$$R\big(\{(\rho_\theta(y_i a_i))_i : a \in \operatorname{conv} B\}\big) \le \frac{R(B)}{\theta},$$

where $\rho_\theta$ is the [ramp cost](ramp.md) and $R$ the [empirical Rademacher complexity](rademacher-complexity.md). It is [the general bound](rademacher-complexity-margin-costs-conve.md) with $L = 1/\theta$.

In a margin bound of the form "true error $\le$ empirical ramp cost $+$ $2\,\mathbb{E}R(\text{costs})$ $+$ deviation", this term is what makes the bound independent of the number of voted classifiers: it pays $1/\theta$ times the complexity of the base class, and the empirical ramp cost is at most the fraction of training points with margin at most $\theta$ ([upper bound](ramp-le-indicator.md)).

## Background

- [AdaBoost's training margins](../../online-learning-and-boosting/adaboost/margin-err-le.md): AdaBoost drives that fraction down exponentially fast.

## Sources

- P. L. Bartlett and S. Mendelson, "Rademacher and Gaussian complexities: risk bounds and structural results", *J. Mach. Learn. Res.* 3 (2002), 463–482, <https://jmlr.csail.mit.edu/papers/volume3/bartlett02a/bartlett02a.pdf>, Theorem 12, parts 2 and 4 (in the convention used here, as in [the general bound](rademacher-complexity-margin-costs-conve.md)); the bounded quantity is the complexity term of their Theorem 7 with $L = 1/\theta$.
