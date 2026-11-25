# Expected statistics are the design matrix times the parameters

Let a [stratified LD-score model](model.md) on a measure $\mu$ have $N \ne 0$ individuals, let $\mathcal{C}$ be a finite set of annotations with values $a_{kC}$ and coefficients $\tau_C$ such that $\sigma^2_k = \sum_{C} \tau_C\, a_{kC}$ for every marker $k$, and let $X$ be a [standardized](../ld-score-regression/is-standardized.md) real $N \times M$ genotype matrix. Then for every marker $j$,

$$\int \chi^2_j \, d\mu = (D\theta)_j, \qquad \theta_\ast = \sigma^2_e,\ \theta_C = \tau_C,$$

where $\chi^2_j$ is the [association statistic](chi-sq.md) and $D$ the [design matrix](design.md). Hence the parameters $(\sigma^2_e, \tau)$ are determined by the expected statistics of all markers, whatever their values, exactly when $D$ has full column rank ([injectivity criterion](injective-mul-vec-iff-rank-eq-card.md)).
