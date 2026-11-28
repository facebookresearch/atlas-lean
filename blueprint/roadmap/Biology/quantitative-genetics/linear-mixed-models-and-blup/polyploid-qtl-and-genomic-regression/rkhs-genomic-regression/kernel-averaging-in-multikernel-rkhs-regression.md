# Kernel averaging in multikernel RKHS regression

Given kernel matrices $\mathbf K_1, \dots, \mathbf K_L$ (for instance a [Gaussian kernel](bayesian-rkhs-regression-with-a-gaussian-kernel.md) at bandwidths $h_1, \dots, h_L$), the multikernel model is

$$y = \mathbf 1\mu + \sum_{l=1}^L u_l + \varepsilon, \qquad p(\mu, u_1, \dots, u_L, \varepsilon) \propto \prod_{l=1}^L N(u_l \mid \mathbf 0, \mathbf K_l \sigma_{u_l}^2)\, N(\varepsilon \mid \mathbf 0, I\sigma_\varepsilon^2).$$

**Proposition.** For known variance components, the model is equivalent to a single-kernel model $y = \mathbf 1\mu + u + \varepsilon$ with $u \sim N(\mathbf 0, \bar{\mathbf K}\sigma_u^2)$, where

$$\sigma_u^2 = \sum_{l=1}^L \sigma_{u_l}^2, \qquad \bar{\mathbf K} = \sum_{l=1}^L \frac{\sigma_{u_l}^2}{\sigma_u^2}\, \mathbf K_l .$$

Fitting the variance components therefore learns a data-weighted average kernel, a computationally cheap substitute for treating $h$ as random.

## Depends on

- [Bayesian RKHS regression with a Gaussian kernel](bayesian-rkhs-regression-with-a-gaussian-kernel.md)

## Expansion

Independent Gaussian vectors add: $\sum_l u_l$ is $N(\mathbf 0, \sum_l \sigma_{u_l}^2 \mathbf K_l)$, which factors as $\sigma_u^2 \bar{\mathbf K}$, and a convex combination of positive semidefinite matrices is positive semidefinite, so $\bar{\mathbf K}$ is again a valid kernel. Sampling $h$ directly would require recomputing the kernel at every update; kernel averaging fixes a grid of bandwidths and lets the posterior distribution of the variance components select among them. The same construction combines unrelated kernels, such as a pedigree relationship matrix and a marker-based kernel, in one model.

## Sources

- P. Pérez and G. de los Campos, "Genome-Wide Regression and Prediction with the BGLR Statistical Package", *Genetics* (2014), <https://doi.org/10.1534/genetics.114.164442> (PMC4196607; Equation (3) and Example 5).
