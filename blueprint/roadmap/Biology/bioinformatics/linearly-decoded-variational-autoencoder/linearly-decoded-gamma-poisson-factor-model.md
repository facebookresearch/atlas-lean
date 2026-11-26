# Linearly decoded Gamma–Poisson factor model

**Model.** For cells $n$ and genes $g = 1, \dots, G$, let $z_n \in \mathbb{R}^D$ be a latent cell representation, $s_n > 0$ a count depth and $W \in \mathbb{R}^{G \times D}$ a loading matrix with rows $w_g$. The linearly decoded variational autoencoder (LDVAE) generative model is

$$z_n \sim \mathcal{N}(0, I_D), \quad s_n \sim \mathrm{LogNormal}(s_\mu, s_\sigma^2), \quad \mu_n = \mathrm{softmax}(W z_n), \quad v_{ng} \sim \mathrm{Gamma}(\theta_g, \mu_{ng}), \quad y_{ng} \sim \mathrm{Poisson}(v_{ng} s_n),$$

with the Gamma parameterized by shape $\theta_g > 0$ and mean $\mu_{ng}$. Inference uses a nonlinear neural encoder $q(z_n, s_n \mid y_n)$, as in scVI; only the decoder is linear. A variant draws $z_n$ from a logistic-normal law on the simplex.

**Proposition.**

1. Conditionally on $(z_n, s_n)$, the counts $y_{ng}$ are independent and negative binomial with mean $s_n \mu_{ng}$ and inverse dispersion $\theta_g$: $\mathrm{Var}(y_{ng} \mid z_n, s_n) = s_n\mu_{ng} + (s_n\mu_{ng})^2/\theta_g$.
2. For any genes $g, g'$, $\log(\mu_{ng}/\mu_{ng'}) = (w_g - w_{g'})^{\top} z_n$, so relative expression is log-linear in the cell coordinates and each coordinate $d$ shifts the log-ratio by $w_{gd} - w_{g'd}$ per unit.
3. The model is unchanged if a common vector $c \in \mathbb{R}^D$ is added to every row of $W$ (softmax invariance), so loadings are identified only up to this shift.

## Expansion

Item 1 is the Gamma–Poisson mixture: integrating $\mathrm{Poisson}(v s)$ against a Gamma law with shape $\theta$ and mean $\mu$ gives the negative binomial with mean $s\mu$ and variance $s\mu + (s\mu)^2/\theta$. Item 2 holds because the softmax normalizer cancels in the ratio, and item 3 because adding $c^\top z_n$ to every logit leaves the softmax unchanged. Replacing the scVI neural decoder $f_W(z_n)$ by the linear map $W z_n$ increases reconstruction error but turns the columns of $W$ into gene programs, as in PCA or factor analysis, while keeping amortized variational inference that scales to hundreds of thousands of cells.

## Sources

- V. Svensson, A. Gayoso, N. Yosef and L. Pachter, *Interpretable factor models of single-cell RNA-seq via variational autoencoders*, Bioinformatics (2020). <https://doi.org/10.1093/bioinformatics/btaa169> (PMCID: PMC7267837). Section 2 "Materials and methods".
- R. Lopez, J. Regier, M. B. Cole, M. I. Jordan and N. Yosef, *Deep generative modeling for single-cell transcriptomics*, Nature Methods (2018). <https://doi.org/10.1038/s41592-018-0229-2>
