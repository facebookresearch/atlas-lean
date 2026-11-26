# Posterior latent factors of a spatial multi-modal probabilistic PCA

Let $n$ spots have spatial coordinates $s_1, \dots, s_n$ and let $K$ modalities (for example RNA and protein) be measured at each spot, modality $k$ giving an $m_k \times n$ matrix $Y_k$. The model is

$$Y_k = W_k Z + E_k, \qquad (E_k)_{ji} \overset{\text{iid}}{\sim} N(0, \sigma_k^2), \qquad k = 1, \dots, K,$$

with a shared $d \times n$ latent matrix $Z$ whose rows $Z_1, \dots, Z_d$ are independent, independent of the noise matrices $E_1, \dots, E_K$, and each distributed according to the spatial prior

$$Z_l \sim \mathrm{MVN}(0, \Sigma), \qquad \Sigma_{ij} = k_\gamma(s_i, s_j), \quad l = 1, \dots, d,$$

so that the prior on $Z$ is the product $\prod_l \mathrm{MVN}(Z_l; 0, \Sigma)$, for a positive-definite kernel $k_\gamma$ (by default Matérn with $\nu = 3/2$, $k_\gamma(s,s') = \bigl(1 + \sqrt3\,\|s - s'\|/\gamma\bigr)\,e^{-\sqrt3\,\|s - s'\|/\gamma}$ with length scale $\gamma$). For identifiability the loadings are orthonormal, $W_k^{T}W_k = I_d$, with columns $w_{kl}$. Modality weights $\alpha_k > 0$ balance contributions in the joint (weighted) likelihood.

**Lemma.** Given $Z$, $p(Y_k \mid Z) \propto (\sigma_k^2)^{-m_k n/2}\exp\bigl(-\operatorname{tr}[(Y_k - W_k Z)(Y_k - W_k Z)^{T}]/(2\sigma_k^2)\bigr)$.

**Theorem (posterior of the latent factors).** With shared spatial covariance $\Sigma$, the weighted posterior of each factor is

$$Z_l^{T} \mid Y_1, \dots, Y_K \sim \mathrm{MVN}\!\left(P^{-1} b_l,\ P^{-1}\right), \qquad P = \sum_{k=1}^K \frac{\alpha_k}{\sigma_k^2}\, I_n + \Sigma^{-1}, \qquad b_l = \sum_{k=1}^K \frac{\alpha_k}{\sigma_k^2}\, Y_k^{T} w_{kl},$$

and the factors $Z_1, \dots, Z_d$ are a posteriori independent. Plugging in maximum-marginal-likelihood estimates of $W_k$, $\sigma_k^2$ and $\gamma$ gives the low-dimensional representation $\hat Z_l^{T} = P^{-1} b_l$. With a single modality ($K = 1$) this reduces to spatial PCA of one data matrix.

## Expansion

Because $W_k^{T}W_k = I_d$, the weighted log-likelihood $-\sum_k \frac{\alpha_k}{2\sigma_k^2}\|Y_k - W_k Z\|_F^2$ is, up to constants, $\sum_l \bigl[-\tfrac12 \sum_k \frac{\alpha_k}{\sigma_k^2}\|Z_l\|^2 + Z_l \cdot \sum_k \frac{\alpha_k}{\sigma_k^2} Y_k^{T} w_{kl}\bigr]$. It separates over factors and is quadratic in each $Z_l$, so combining with the product Gaussian prior, whose log-density $-\tfrac12 \sum_l Z_l \Sigma^{-1} Z_l^{T}$ also separates over factors, and completing the square gives precision $P$ and mean $P^{-1}b_l$, with a posterior that factorises over $l$. Orthonormal loadings separate only the likelihood: with marginal $\mathrm{MVN}(0,\Sigma)$ rows that are dependent (for one spot, two factors and $Z_1 = Z_2 \sim N(0,1)$) the posterior is supported on the diagonal and is not this product, so the independence of the rows in the prior is needed. The posterior mean is a spatial smoothing of the modality-weighted projections $Y_k^{T}w_{kl}$: since $P^{-1} = \Sigma(I + c\,\Sigma)^{-1}$ with $c = \sum_k \alpha_k/\sigma_k^2$, noisier modalities (large $\sigma_k^2$) are shrunk more strongly toward the spatial prior. A shared $\Sigma$ across factors also admits a closed-form maximizer of the marginal likelihood for $W_k$ through an eigendecomposition, at $O(n^3)$ cost. Clustering $\hat Z$ then identifies spatial domains.

## Sources

- M. Chen, R. Cheng, J. He, J. Chen, J. Zhang, "SMOPCA: spatially aware dimension reduction integrating multi-omics improves the efficiency of spatial domain detection", Genome Biology (2025), Methods, Eqs. (1)–(6), Lemma 1, Theorem 1 and Corollary 1, <https://doi.org/10.1186/s13059-025-03576-9>, PMCID PMC12096709.
