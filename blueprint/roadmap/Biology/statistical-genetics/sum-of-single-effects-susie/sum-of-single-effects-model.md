# Sum of Single Effects (SuSiE) model and factored variational family

Let $X \in \mathbb{R}^{n \times p}$ be a design matrix, $y \in \mathbb{R}^n$ a response vector,
$L \ge 1$ the number of single-effect components, $\sigma^2 > 0$ the residual variance,
$\sigma_{01}^2, \dots, \sigma_{0L}^2 > 0$ prior effect variances, and $\pi \in \Delta_{p-1}$
a vector of prior inclusion probabilities with $\pi_j > 0$ for all $j = 1, \dots, p$.

The **Sum of Single Effects (SuSiE)** regression model specifies

$$y = X b + e, \qquad e \sim \mathcal{N}_n(0, \sigma^2 I_n), \qquad b = \sum_{l=1}^L b_l,$$

where

$$b_l = \gamma_l \beta_l, \qquad \gamma_l \sim \operatorname{Multinomial}(1, \pi), \qquad \beta_l \sim \mathcal{N}(0, \sigma_{0l}^2),$$

and the $2L + 1$ random elements $\gamma_1, \beta_1, \dots, \gamma_L, \beta_L, e$ are mutually independent: within each
component the selector $\gamma_l$ is drawn independently of the effect size $\beta_l$, the pairs
$(\gamma_l, \beta_l)$ are independent across $l$, and the noise $e$ is independent of all of them. Equivalently,
given $b_1, \dots, b_L$, the response has law $y \mid b_1, \dots, b_L \sim \mathcal{N}_n\bigl(X \sum_{l} b_l, \sigma^2 I_n\bigr)$.

Each $b_l$ has at most one nonzero coordinate; its law $g_l$, the law of $\gamma_l \beta_l$ with $\gamma_l$ and
$\beta_l$ independent as above, is the single-effect regression (SER) prior with variance $\sigma_{0l}^2$.

The **SuSiE variational family** consists of distributions on $(b_1, \dots, b_L)$ that factor across
effects,

$$q(b_1, \dots, b_L) = \prod_{l=1}^L q_l(b_l),$$

without requiring factorization across coordinates within each $q_l$. For factors $q_l$ on $\mathbb{R}^p$ with
finite second moments, the evidence lower bound (ELBO) is

$$F(q_1, \dots, q_L; \sigma^2, \sigma_0^2) = \mathbb{E}_q\bigl[\log p(y \mid X, b_1, \dots, b_L, \sigma^2)\bigr] - \sum_{l=1}^L D_{\mathrm{KL}}(q_l \,\|\, g_l) \in [-\infty, \infty),$$

which equals $\mathbb{E}_q[\log p(y, b_1, \dots, b_L \mid X, \sigma^2, \sigma_0^2)] - \mathbb{E}_q[\log q(b_1, \dots, b_L)]$
whenever $q$ has a density with respect to the prior, and is $-\infty$ when some $q_l$ has infinite divergence
from $g_l$.

A **level-$\rho$ credible set** for the multiple regression model is a subset $S \subseteq \{1, \dots, p\}$
having posterior probability at least $\rho$ of containing at least one variable with nonzero regression coefficient.

## Sources

- G. Wang, A. Sarkar, P. Carbonetto, and M. Stephens, "A Simple New Approach to Variable Selection in Regression, with Application to Genetic Fine Mapping", Journal of the Royal Statistical Society Series B 82 (2020), 1273–1300, <https://doi.org/10.1111/rssb.12388> (PMC10201948).
