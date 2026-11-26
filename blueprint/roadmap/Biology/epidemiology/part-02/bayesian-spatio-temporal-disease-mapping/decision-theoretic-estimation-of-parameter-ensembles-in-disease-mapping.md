# Decision-theoretic estimation of parameter ensembles in disease mapping

**Setting.** In a two-stage Bayesian hierarchical model, data $\mathbf{y}$ inform an ensemble of unit-specific parameters $\boldsymbol\theta = (\theta_1, \dots, \theta_n)$, such as the relative risks of $n$ geographical areas or hospitals in spatial epidemiology. Reporting the ensemble means choosing point estimates $\boldsymbol\delta = (\delta_1, \dots, \delta_n)$ that minimize a posterior expected loss, and different inferential goals call for different losses.

**Theorem (Ghosh-Louis: posterior means are underdispersed).** For $n \ge 2$,

$$
\mathbb{E}\Big[\frac1n\sum_{i=1}^n(\theta_i - \bar\theta)^2\,\Big|\,\mathbf{y}\Big] \ \ge\ \frac1n\sum_{i=1}^n\Big(\mathbb{E}[\theta_i\mid\mathbf{y}] - \frac1n\sum_{k=1}^n\mathbb{E}[\theta_k\mid\mathbf{y}]\Big)^2, \qquad \bar\theta = \frac1n\sum_i\theta_i,
$$

with equality if and only if every $\theta_i-\bar\theta$ has a degenerate posterior distribution: the ensemble of posterior means (the minimizer of summed squared error loss, SSEL) is shrunk and understates the spread of the true ensemble.

**Theorem (constrained Bayes estimator).** Among estimates whose ensemble mean and ensemble variance match the posterior expected mean and variance of the true ensemble, SSEL is minimized by

$$
\hat\theta^{\mathrm{CB}}_i = \omega\,\hat\theta_i + (1 - \omega)\,\bar{\hat\theta}, \qquad \omega = \Bigg[1 + \frac{n^{-1}\sum_i \operatorname{Var}[\theta_i - \bar\theta\mid\mathbf{y}]}{n^{-1}\sum_i(\hat\theta_i - \bar{\hat\theta})^2}\Bigg]^{1/2},
$$

where $\hat\theta_i = \mathbb{E}[\theta_i\mid\mathbf{y}]$, $\bar{\hat\theta} = n^{-1}\sum_i\hat\theta_i$, the posterior means are not all equal, and

$$
\frac1n\sum_{i=1}^n\operatorname{Var}[\theta_i - \bar\theta\mid\mathbf{y}] = \frac1n\sum_{i=1}^n\operatorname{Var}[\theta_i\mid\mathbf{y}] - \operatorname{Var}[\bar\theta\mid\mathbf{y}].
$$

Since $\omega \ge 1$, the posterior means are stretched away from their mean.

**Proposition (threshold classification).** For a threshold $C$ (for example a relative risk above which an area is flagged) and a weight $p \in [0,1]$, define the weighted threshold classification loss

$$
\mathrm{TCL}_p(C, \boldsymbol\theta, \boldsymbol\delta) = \frac1n\sum_{i=1}^n \Big(p\,\mathbf{1}\{\theta_i \le C,\ \delta_i > C\} + (1 - p)\,\mathbf{1}\{\theta_i > C,\ \delta_i \le C\}\Big),
$$

a weighted average of the false-positive and false-negative rates. It is minimized in posterior expectation by the vector of posterior $(1 - p)$-quantiles,

$$
\boldsymbol\theta^{\mathrm{TCL}}_{(1-p)} = \big(Q_{\theta_1\mid\mathbf{y}}(1 - p), \dots, Q_{\theta_n\mid\mathbf{y}}(1 - p)\big).
$$

For the unweighted loss ($p = 1/2$) the vector of posterior medians is optimal; the minimizer is not unique.

**Proposition (rank classification).** For classifying units by whether their percentile rank exceeds $\gamma$, the optimal percentile ranks are obtained by ranking the posterior probabilities $\mathbb{P}[P_i(\boldsymbol\theta) \ge \gamma\mid\mathbf{y}]$.

## Expansion

The Ghosh-Louis inequality is the law of total variance applied to the empirical variance of the ensemble: the posterior expected spread equals the spread of the posterior means plus $n^{-1}\sum_i\operatorname{Var}[\theta_i-\bar\theta\mid\mathbf{y}]$, the average posterior variance minus $\operatorname{Var}[\bar\theta\mid\mathbf{y}]$. For example, with $n=2$ and independent posteriors $\theta_1\sim N(-1,1)$, $\theta_2\sim N(1,1)$, the expected spread is $1+\tfrac12=\tfrac32$, so $\omega=\sqrt{3/2}$; Theorem 2 of the thesis prints the weight with the average posterior variance alone, which is exact only when $\operatorname{Var}[\bar\theta\mid\mathbf{y}]=0$. The constrained Bayes estimator restores the expected spread with the smallest SSEL penalty, by an affine stretch of the posterior means around their average with the factor $\omega$. The TCL result reduces to unit-wise decisions: classifying unit $i$ above $C$ costs $p\,\mathbb{P}(\theta_i \le C\mid\mathbf{y})$ in expectation, and classifying it below costs $(1-p)\,\mathbb{P}(\theta_i > C\mid\mathbf{y})$. The optimal rule flags $i$ exactly when $\mathbb{P}(\theta_i > C\mid\mathbf{y}) > p$, which is equivalent to the posterior $(1-p)$-quantile exceeding $C$. Simulations of spatial disease-mapping models (such as the BYM model for schizophrenia counts and for MRSA prevalence in hospitals) show that triple-goal and quantile-based estimators trade little SSEL efficiency for much better ensemble-level and classification performance.

## Depends on

- [Quantile function of a real measure](../../../../Probability/distributions/distribution-functions/quantile-function-and-inverse-transform-sampling/quantile-function/cdf-quantile.md)

## Proof depends on

- [The quantile function as a generalized inverse of the cdf](../../../../Probability/distributions/distribution-functions/quantile-function-and-inverse-transform-sampling/quantile-function/cdf-quantile-le-iff.md)

## Sources

- Cedric E. Ginestet, "Bayesian Decision-theoretic Methods for Parameter Ensembles with Application to Epidemiology", arXiv (2011), Section 2.2 (Theorem 1, Ghosh-Louis theorem), Section 2.4 (Theorem 2, constrained Bayes estimator), Section 4.2 (threshold and rank classification losses, Proposition 1, Corollary 1, Proposition 2), <https://doi.org/10.48550/arXiv.1105.5004>.
- Cedric E. Ginestet, Nicky G. Best, Sylvia Richardson, "Classification loss function for parameter ensembles in Bayesian hierarchical models", Statistics & Probability Letters 82 (2012), 859–863 (threshold and rank classification losses), <https://doi.org/10.1016/j.spl.2011.12.015>.
- T. A. Louis, "Estimating a population of parameter values using Bayes and empirical Bayes methods", Journal of the American Statistical Association 79 (1984), 393–398, <https://doi.org/10.1080/01621459.1984.10478062>.
