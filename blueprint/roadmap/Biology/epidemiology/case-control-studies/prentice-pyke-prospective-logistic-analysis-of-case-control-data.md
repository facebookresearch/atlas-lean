# Prentice–Pyke: prospective logistic analysis of case–control data

Suppose disease incidence follows the logistic model $P(D = 1 \mid x) = \operatorname{expit}(\alpha + \beta^\top x)$ in the population, and cases and controls are sampled with probabilities that depend only on $D$. Prentice and Pyke (1979) established that the maximum-likelihood estimator of the log odds-ratio parameter $\beta$ from the case–control data, and its asymptotic covariance matrix, are those obtained by fitting the prospective logistic regression to the case–control sample, so the simpler prospective model may be used to analyse data gathered retrospectively (Byrne and Dawid 2014, Introduction and Section 3). Only the intercept changes: if the sampling fractions of cases and controls are $\pi_1$ and $\pi_0$, Bayes' rule gives, for a sampled individual with covariates $x$, $P(D = 1 \mid x, \text{sampled}) = \operatorname{expit}(\alpha^* + \beta^\top x)$ with $\alpha^* = \alpha + \ln(\pi_1/\pi_0)$.

## Expansion

1. The model: the population logistic model, the retrospective sampling design with fixed numbers of cases and controls, and the nonparametric law of the covariates.
2. The shifted intercept for the sampled conditional probability, by Bayes' rule.
3. The profile-likelihood argument: maximizing the retrospective likelihood over the covariate law reduces to the prospective logistic likelihood for $\beta$.
4. Asymptotic normality of the estimator of $\beta$ and the equality of the two asymptotic covariance matrices.
5. The extension to strong meta Markov models and the Bayesian counterpart of Byrne and Dawid, as separate statements.

## Sources

- S. P. J. Byrne and A. P. Dawid, Retrospective–prospective symmetry in the likelihood and Bayesian analysis of case–control studies, Biometrika 101 (2014), 189–204. <https://arxiv.org/abs/1202.2683>
- Original result: R. L. Prentice and R. Pyke, Logistic disease incidence models and case-control studies, Biometrika 66 (1979), 403–411. <https://doi.org/10.1093/biomet/66.3.403> The equality of the estimators and of their asymptotic covariance matrices follows Byrne and Dawid.
