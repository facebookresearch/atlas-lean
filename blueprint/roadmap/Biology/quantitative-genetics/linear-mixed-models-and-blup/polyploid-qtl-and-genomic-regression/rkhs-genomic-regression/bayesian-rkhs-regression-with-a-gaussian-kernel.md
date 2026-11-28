# Bayesian RKHS regression with a Gaussian kernel

Let $y \in \mathbb R^n$ be phenotypes and $x_i \in \mathbb R^p$ the marker genotype vector of individual $i$. A **reproducing kernel** is a map $K : \mathbb R^p \times \mathbb R^p \to \mathbb R$ that is positive semidefinite: $\sum_{i,i'} \alpha_i \alpha_{i'} K(x_i, x_{i'}) \ge 0$ for all real $\alpha$. Write $\mathbf K = \{K(x_i, x_{i'})\}$ for the $n \times n$ kernel matrix.

**Model.** The Bayesian RKHS regression is

$$y = \mathbf 1\mu + u + \varepsilon, \qquad p(\mu, u, \varepsilon) \propto N(u \mid \mathbf 0, \mathbf K\sigma_u^2)\, N(\varepsilon \mid \mathbf 0, I\sigma_\varepsilon^2),$$

with a flat prior on $\mu$ and scaled inverse-$\chi^2$ priors on $\sigma_u^2$ and $\sigma_\varepsilon^2$. Its structure is that of the animal model, with the pedigree numerator relationship matrix replaced by $\mathbf K$; with $\mathbf K$ a genomic relationship matrix it is genomic BLUP.

**Gaussian kernel.** A standard choice is

$$K(x_i, x_{i'}) = \exp\Bigl\{-h\, \frac{1}{p}\sum_{k=1}^p (x_{ik} - x_{i'k})^2\Bigr\},$$

with bandwidth $h > 0$ controlling how fast genetic covariance decays with average squared genotype distance. Too small an $h$ makes $\mathbf K$ nearly the all-ones matrix, confounded with the intercept; too large an $h$ makes $\mathbf K$ nearly the identity, confounded with the residual. A practical grid is $h \in \{\tfrac15, 1, 5\} \times 1/M$, with $M$ the median off-diagonal squared distance, giving median kernel entries $e^{-1/5}$, $e^{-1}$, $e^{-5}$.

## Depends on

- [BLUP as a conditional law](../../cond-distrib-mixed-model.md)

## Expansion

By the representer theorem the posterior mean of $u$ lies in the span of the kernel sections $K(\cdot, x_i)$, so the regression function is a linear combination of $n$ basis functions and the effective dimension is $n$ even when $p \gg n$. Given the variance components, the posterior mean of $u$ is the BLUP $\sigma_u^2 \mathbf K(\sigma_u^2\mathbf K + \sigma_\varepsilon^2 I)^{-1}(y - \mathbf 1\mu)$. The Gaussian kernel can capture non-additive genetic signal that a linear kernel misses. BGLR samples the model by Gibbs sampling, working with the eigendecomposition of $\mathbf K$.

## Sources

- P. Pérez and G. de los Campos, "Genome-Wide Regression and Prediction with the BGLR Statistical Package", *Genetics* (2014), <https://doi.org/10.1534/genetics.114.164442> (PMC4196607; Equation (2), Example 4, and the section on Gaussian processes).
