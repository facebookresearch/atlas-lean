# ELBO monotonicity and KL minimization of IBSS

Let Iterative Bayesian Stepwise Selection (IBSS) be the cyclic algorithm that, at each inner step
$l = 1, \dots, L$, updates $q_l \leftarrow \operatorname{SER}(X, \bar r_l; \sigma^2, \sigma_{0l}^2)$
using the current expected residuals $\bar r_l = y - X \sum_{l' \ne l} \bar b_{l'}$, started from factors
with finite second moments and finite divergence from their SER priors.
Then IBSS is a coordinate-ascent algorithm for maximizing the ELBO $F(q_1, \dots, q_L; \sigma^2, \sigma_0^2)$
over the factored variational family $q = \prod_{l=1}^L q_l$, and equivalently a coordinate-descent
algorithm for minimizing $D_{\mathrm{KL}}(q \,\|\, p_{\mathrm{post}})$ where $p_{\mathrm{post}}$
is the exact SuSiE posterior. In particular, $F$ is non-decreasing at every IBSS update.

## Depends on

- [Sum of Single Effects (SuSiE) model and factored variational family](sum-of-single-effects-model.md)
- [IBSS coordinate-ascent update reduces to single-effect regression](ibss-coordinate-ascent-ser-update.md)

## Expansion

Since $F(q) = \log p(y \mid X, \sigma^2, \sigma_0^2) - D_{\mathrm{KL}}(q \,\|\, p_{\mathrm{post}})$
and each IBSS step replaces $q_l$ by its exact ELBO maximizer from Proposition 1, every update
increases (or maintains) $F(q)$ and decreases (or maintains) $D_{\mathrm{KL}}(q \,\|\, p_{\mathrm{post}})$.

## Sources

- G. Wang, A. Sarkar, P. Carbonetto, and M. Stephens, "A Simple New Approach to Variable Selection in Regression, with Application to Genetic Fine Mapping", Journal of the Royal Statistical Society Series B 82 (2020), 1273–1300, <https://doi.org/10.1111/rssb.12388> (PMC10201948). (Corollary 1.)
