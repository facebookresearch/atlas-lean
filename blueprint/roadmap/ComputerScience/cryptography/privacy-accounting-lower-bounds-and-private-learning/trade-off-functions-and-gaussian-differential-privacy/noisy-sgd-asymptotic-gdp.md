# Noisy stochastic gradient descent is asymptotically Gaussian differentially private

Consider NoisySGD (Dong–Roth–Su, Algorithm 1) on a dataset of $n$ records: for $T$ iterations it takes a uniformly random subsample of exactly $m$ records without replacement (sampling ratio $p = m/n$), clips each per-example gradient to $\ell_2$ norm at most $C$, adds $\mathcal{N}(0, 4\sigma^2C^2/m^2 \cdot I)$ to the average of the clipped gradients (equivalently, noise of standard deviation $2C\sigma$ per coordinate to their sum, matching the replace-one sensitivity $2C$ of the sum), and takes a gradient step; it outputs the final iterate $\theta_T$ and never releases the subsampled indices. The privacy accounting below covers the whole trajectory $(\theta_1, \dots, \theta_T)$, so the same bound holds if all iterates are released, but the algorithm's output is $\theta_T$. Each step is then $1/\sigma$-GDP on the subsample, and NoisySGD is $C_{m/n}(G_{1/\sigma})^{\otimes T}$-DP, where $C_p$ is the subsampling operator. If $T \to \infty$ and $m\sqrt{T}/n \to c > 0$ with $\sigma$ fixed, this composed privacy bound converges uniformly to $G_\mu$ with

$$
\mu = \sqrt{2}\,c\,\sqrt{e^{\sigma^{-2}}\,\Phi\bigl(1.5\,\sigma^{-1}\bigr) + 3\,\Phi\bigl(-0.5\,\sigma^{-1}\bigr) - 2},
$$

so NoisySGD is asymptotically $\mu$-GDP. The statement concerns the privacy bound, not the exact trade-off function of the mechanism, which can be strictly larger (for constant gradients the output reveals nothing about the data). A Poisson-sampling variant has a different limit and needs its own theorem. In Dong, Roth and Su's three MNIST runs (Figure 7), this limit gives a tighter privacy bound than the moments accountant; that comparison is empirical and limited to those runs.

## Proof sketch

Each step is a subsampled Gaussian mechanism: the average of clipped gradients has sensitivity $2C/m$ under replacement, so the step is $1/\sigma$-GDP on the subsample, $C_{m/n}(G_{1/\sigma})$-DP by the subsampling theorem, and the run is $C_{m/n}(G_{1/\sigma})^{\otimes T}$-DP by composition. For a symmetric trade-off function $f$ with $f(0) = 1$ and $\int_0^1 (f'(x) + 1)^4\,dx < \infty$, the central limit theorem for composition gives $C_p(f)^{\otimes T} \to G_{p_0\sqrt{2\chi^2_+(f)}}$ when $p\sqrt T \to p_0$, where $\chi^2_+(f) = \int_0^1 (|f'(x)| - 1)_+^2\,dx$; for $f = G_{1/\sigma}$ one computes $\chi^2_+(G_\mu) = e^{\mu^2}\Phi(3\mu/2) + 3\Phi(-\mu/2) - 2$, which gives the formula.

## Depends on

- [Gaussian differential privacy](gaussian-differential-privacy.md)

## Proof depends on

- [Central limit theorem for the composition of trade-off functions](f-dp-composition-central-limit-theorem.md)
- [Subsampling theorem for f-differential privacy](f-dp-subsampling-theorem.md)
- [The Gaussian mechanism is exactly Gaussian differentially private](gaussian-mechanism-gdp.md)

## Sources

- J. Dong, A. Roth, W. J. Su, "Gaussian Differential Privacy", Journal of the Royal Statistical Society Series B 84 (2022), arXiv:1905.02383v3, Algorithm 1, Theorems 5.1 and 5.2, Lemma 5.3, Corollary 5.4 and Figure 7.
- M. Abadi, A. Chu, I. Goodfellow, H. B. McMahan, I. Mironov, K. Talwar, L. Zhang, "Deep Learning with Differential Privacy", ACM CCS (2016), arXiv:1607.00133.
