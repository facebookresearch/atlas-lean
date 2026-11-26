# Sum of Single Effects (SuSiE) model and factored variational family

Let $X \in \mathbb{R}^{n \times p}$ be a design matrix, $y \in \mathbb{R}^n$ a response vector,
$L \ge 1$ the number of single-effect components, $\sigma^2 > 0$ the residual variance,
$\sigma_{01}^2, \dots, \sigma_{0L}^2 > 0$ prior effect variances, and $\pi \in \Delta_{p-1}$
a vector of prior inclusion probabilities with $\pi_j > 0$ for all $j = 1, \dots, p$.

The **Sum of Single Effects (SuSiE)** regression model specifies

$$y = X b + e, \qquad e \sim \mathcal{N}_n(0, \sigma^2 I_n), \qquad b = \sum_{l=1}^L b_l,$$

where the components $(b_1, \dots, b_L)$ are independent with

$$b_l = \gamma_l \beta_l, \qquad \gamma_l \sim \operatorname{Multinomial}(1, \pi), \qquad \beta_l \sim \mathcal{N}(0, \sigma_{0l}^2).$$

Each $b_l$ has at most one nonzero coordinate and follows a single-effect regression (SER) prior.

The **SuSiE variational family** consists of distributions on $(b_1, \dots, b_L)$ that factor across
effects,

$$q(b_1, \dots, b_L) = \prod_{l=1}^L q_l(b_l),$$

without requiring factorization across coordinates within each $q_l$. Its evidence lower bound (ELBO) is

$$F(q_1, \dots, q_L; \sigma^2, \sigma_0^2) = \mathbb{E}_q[\log p(y, b_1, \dots, b_L \mid X, \sigma^2, \sigma_0^2)] - \mathbb{E}_q[\log q(b_1, \dots, b_L)].$$

A **level-$\rho$ credible set** for the multiple regression model is a subset $S \subseteq \{1, \dots, p\}$
having posterior probability at least $\rho$ of containing at least one variable with nonzero regression coefficient.

## Depends on

- [Posterior inclusion probabilities under single-effect regression](../bayesian-fine-mapping-and-colocalization/ser-posterior-eq-pip.md)
- [Credible set](../bayesian-fine-mapping-and-colocalization/is-credible-set.md)

## Sources

- G. Wang, A. Sarkar, P. Carbonetto, and M. Stephens, "A Simple New Approach to Variable Selection in Regression, with Application to Genetic Fine Mapping", Journal of the Royal Statistical Society Series B 82 (2020), 1273–1300, <https://doi.org/10.1111/rssb.12388> (PMC10201948).
