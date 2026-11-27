# IBSS coordinate-ascent update reduces to single-effect regression

For $r \in \mathbb{R}^n$, let $\operatorname{SER}(X, r; \sigma^2, \sigma_{0}^2)$ denote the posterior law of $b$ in
the single-effect regression $r = X b + e$, $e \sim \mathcal{N}_n(0, \sigma^2 I_n)$, with $b$ drawn from the SER
prior of the [SuSiE model](sum-of-single-effects-model.md) with variance $\sigma_0^2$ (selector and effect size
independent) and $e$ independent of $b$. When every column $x_j$
of $X$ is nonzero, this law puts mass $\alpha_j$ on the $j$-th coordinate axis, where $\alpha$ is given by the
[posterior inclusion probabilities of the single-effect regression](../bayesian-fine-mapping-and-colocalization/ser-posterior-eq-pip.md),
and given that axis the effect $b_j$ has the normal law of the
[effect posterior of the single-effect regression](../bayesian-fine-mapping-and-colocalization/cond-distrib-ser-effect.md)
for the column $x_j$.

In the SuSiE model with ELBO $F$ and SER priors $g_1, \dots, g_L$, fix $l \in \{1, \dots, L\}$ and factors
$q_{l'}$ ($l' \ne l$) on $\mathbb{R}^p$ with finite second moments and finite divergence
$D_{\mathrm{KL}}(q_{l'} \,\|\, g_{l'}) < \infty$. Let $\bar b_{l'} = \mathbb{E}_{q_{l'}}[b_{l'}]$ and define the
expected residual vector

$$\bar r_l := y - X \sum_{l' \ne l} \bar b_{l'}.$$

Then, over all distributions $q_l$ on $\mathbb{R}^p$ with finite second moments,
$q_l \mapsto F(q_1, \dots, q_L; \sigma^2, \sigma_0^2)$ attains a finite maximum, and attains it exactly at the
single-effect regression posterior on the expected residuals:

$$\arg\max_{q_l} F(q_1, \dots, q_L; \sigma^2, \sigma_0^2) = \operatorname{SER}(X, \bar r_l; \sigma^2, \sigma_{0l}^2).$$

## Depends on

- [Sum of Single Effects (SuSiE) model and factored variational family](sum-of-single-effects-model.md)
- [Posterior inclusion probabilities of the single-effect regression](../bayesian-fine-mapping-and-colocalization/ser-posterior-eq-pip.md)
- [The effect posterior of the single-effect regression](../bayesian-fine-mapping-and-colocalization/cond-distrib-ser-effect.md)

## Expansion

Expand $\mathbb{E}_q\|y - X\sum_{l'} b_{l'}\|_2^2$ as a function of $q_l$: by independence of the factors and
finiteness of their second moments, it equals $\mathbb{E}_{q_l}\|\bar r_l - X b_l\|_2^2$ plus a finite constant
not depending on $q_l$. With the finite divergences $D_{\mathrm{KL}}(q_{l'} \,\|\, g_{l'})$, $l' \ne l$, also
absorbed into the constant,

$$F = \mathrm{const} + \mathbb{E}_{q_l}[\log p(\bar r_l \mid X, b_l, \sigma^2)] - D_{\mathrm{KL}}(q_l \,\|\, g_l) = \mathrm{const}' - D_{\mathrm{KL}}\bigl(q_l \,\|\, \operatorname{SER}(X, \bar r_l; \sigma^2, \sigma_{0l}^2)\bigr),$$

where $\mathrm{const}'$ adds the finite log marginal likelihood of the single-effect regression on $\bar r_l$.
The divergence is nonnegative and vanishes only at the SER posterior, which has finite second moments.

## Sources

- G. Wang, A. Sarkar, P. Carbonetto, and M. Stephens, "A Simple New Approach to Variable Selection in Regression, with Application to Genetic Fine Mapping", Journal of the Royal Statistical Society Series B 82 (2020), 1273–1300, <https://doi.org/10.1111/rssb.12388> (PMC10201948). (Proposition 1 and Appendix B.)
