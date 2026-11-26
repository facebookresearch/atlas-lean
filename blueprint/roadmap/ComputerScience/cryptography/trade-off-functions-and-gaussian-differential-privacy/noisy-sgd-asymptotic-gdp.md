# Noisy stochastic gradient descent is asymptotically Gaussian differentially private

Consider noisy stochastic gradient descent that, for $T$ iterations, selects a uniformly random mini-batch with sampling probability $p$, clips per-example gradients to norm at most $1$, and adds Gaussian noise $\sigma \cdot \mathcal{N}(0, I)$ to the mini-batch gradient sum. If $T \to \infty$ and $p\sqrt{T} \to \nu > 0$ with $\sigma$ fixed, then the algorithm is asymptotically $\mu$-GDP with

$$
\mu = \nu\sqrt{e^{1/\sigma^2} - 1},
$$

in the sense that its trade-off function converges uniformly to $G_\mu$. This gives tighter privacy accounting than the moments accountant for deep learning with differential privacy.

## Proof sketch

Each iteration is a subsampled Gaussian mechanism with sensitivity one and noise $\sigma$, so it is $C_p(G_{1/\sigma})$-DP by the subsampling theorem, and the whole run is the $T$-fold composition. Computing $\mathrm{kl}$, $\kappa_2$ and $\kappa_3$ of $C_p(G_{1/\sigma})$ to leading order in $p$ gives $\sum \mathrm{kl} \to \tfrac{\nu^2}{2}(e^{1/\sigma^2} - 1)$ and $\sum \kappa_2 \to \nu^2(e^{1/\sigma^2} - 1)$ with vanishing third moments, and the central limit theorem yields $G_{2K/s}$ with $2K/s = \nu\sqrt{e^{1/\sigma^2}-1}$.

## Depends on

- [Central limit theorem for the composition of trade-off functions](f-dp-composition-central-limit-theorem.md)
- [Subsampling theorem for f-differential privacy](f-dp-subsampling-theorem.md)
- [The Gaussian mechanism is exactly Gaussian differentially private](gaussian-mechanism-gdp.md)

## Proof depends on

- [Central limit theorem for the composition of trade-off functions](f-dp-composition-central-limit-theorem.md)
- [Subsampling theorem for f-differential privacy](f-dp-subsampling-theorem.md)
- [The Gaussian mechanism is exactly Gaussian differentially private](gaussian-mechanism-gdp.md)

## Sources

- J. Dong, A. Roth, W. J. Su, "Gaussian Differential Privacy", Journal of the Royal Statistical Society Series B 84 (2022), arXiv:1905.02383.
- M. Abadi, A. Chu, I. Goodfellow, H. B. McMahan, I. Mironov, K. Talwar, L. Zhang, "Deep Learning with Differential Privacy", ACM CCS (2016), arXiv:1607.00133.
