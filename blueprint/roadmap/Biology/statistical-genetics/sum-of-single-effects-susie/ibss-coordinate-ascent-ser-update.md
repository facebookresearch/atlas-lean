# IBSS coordinate-ascent update reduces to single-effect regression

Under the [SuSiE model](sum-of-single-effects-model.md) with factored variational approximation
$q(b_1, \dots, b_L) = \prod_{l=1}^L q_l(b_l)$, fix $l \in \{1, \dots, L\}$ and hold the
other factors $\{q_{l'} : l' \ne l\}$ fixed with finite first and second moments. Let
$\bar b_{l'} = \mathbb{E}_{q_{l'}}[b_{l'}]$ and define the expected residual vector
$$\bar r_l := y - X \sum_{l' \ne l} \bar b_{l'}.$$
Then the unique maximizer of the ELBO $F(q_1, \dots, q_L; \sigma^2, \sigma_0^2)$ over all
distributions $q_l$ is the exact single-effect regression posterior on expected residuals:
$$\arg\max_{q_l} F(q_1, \dots, q_L; \sigma^2, \sigma_0^2) = \operatorname{SER}(X, \bar r_l; \sigma^2, \sigma_{0l}^2).$$

## Depends on

- [Sum of Single Effects (SuSiE) model and factored variational family](sum-of-single-effects-model.md)
- [Posterior inclusion probabilities under single-effect regression](../bayesian-fine-mapping-and-colocalization/ser-posterior-eq-pip.md)

## Expansion

Expanding the expected log-likelihood $-\frac{1}{2\sigma^2} \mathbb{E}_q\|y - X\sum_{l'} b_{l'}\|_2^2$
as a function of $q_l$ alone, all cross terms between $b_l$ and $b_{l'}$ ($l' \ne l$) factor by
independence of $q_l$ and $q_{l'}$ into $-2\,\mathbb{E}_{q_l}[b_l]^\top X^\top (y - X\sum_{l'\ne l} \bar b_{l'})$.
Up to a constant independent of $q_l$, the ELBO in $q_l$ therefore equals the negative KL divergence
$-D_{\mathrm{KL}}(q_l \,\|\, \operatorname{SER}(X, \bar r_l; \sigma^2, \sigma_{0l}^2))$,
which is uniquely maximized at $q_l = \operatorname{SER}(X, \bar r_l; \sigma^2, \sigma_{0l}^2)$.

## Sources

- G. Wang, A. Sarkar, P. Carbonetto, and M. Stephens, "A Simple New Approach to Variable Selection in Regression, with Application to Genetic Fine Mapping", Journal of the Royal Statistical Society Series B 82 (2020), 1273–1300, <https://doi.org/10.1111/rssb.12388> (PMC10201948). (Proposition 1.)
