# AdaBoost's training margins

AdaBoost runs on $m > 0$ training points with labels $y_i \in \{\pm 1\}$ and an arbitrary weak learner; $D_t$ are its weights, $h_t$ the weak hypothesis and $\varepsilon_t$ its weighted error in round $t$, $\alpha_t = \tfrac12 \log((1-\varepsilon_t)/\varepsilon_t)$, and $F_T = \sum_{t<T} \alpha_t h_t$ is the combined score. If every round $t < T$ has $0 < \varepsilon_t < 1$, then for every real $\theta$,

$$\frac{1}{m} \#\Big\{i : y_i F_T(x_i) \le \theta \sum_{t<T} \alpha_t\Big\} \le \prod_{t<T} 2 \sqrt{\varepsilon_t^{1-\theta} (1 - \varepsilon_t)^{1+\theta}}.$$

For $\theta = 0$ this is [the training-error bound](train-err-le-prod-sqrt-of-eps.md). If every $\varepsilon_t \le 1/2 - \gamma$ for a fixed $\gamma > 0$ and $\theta$ is small enough relative to $\gamma$, each factor is below $1$, so AdaBoost drives the fraction of training points with margin at most $\theta$ to zero exponentially fast. Combined with a margin-based generalization bound, which does not depend on the number of rounds, this is the margins explanation of why AdaBoost often does not overfit.

## Informally uses

- [Freund and Schapire's training-error bound with per-round errors](train-err-le-prod-sqrt-of-eps.md): Schapire, Freund, Bartlett and Lee obtain Theorem 5 by extending its proof, bounding the indicator by $\exp(-y F_T(x) + \theta \sum_t \alpha_t)$.

## Background

- [The complexity term of the margin bound for voting classifiers](../../generalization-bounds-and-concentration/rademacher-complexity/rademacher-complexity-ramp-costs-convex.md): the generalization side of the margins explanation.

## Sources

- R. E. Schapire, Y. Freund, P. Bartlett and W. S. Lee, "Boosting the margin: a new explanation for the effectiveness of voting methods", *Ann. Statist.* 26 (1998), 1651–1686, Theorem 5, equation (11).
