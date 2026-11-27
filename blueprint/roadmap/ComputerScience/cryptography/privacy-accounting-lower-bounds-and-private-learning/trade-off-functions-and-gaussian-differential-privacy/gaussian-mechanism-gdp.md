# The Gaussian mechanism is exactly Gaussian differentially private

Let $q : \mathcal{X}^n \to \mathbb{R}^d$ have $\ell_2$-sensitivity $\Delta = \sup_{S \sim S'} \|q(S) - q(S')\|_2$, and let $M(S) = q(S) + \sigma Z$ with $Z \sim \mathcal{N}(0, I_d)$. Then $M$ is $\mu$-GDP with $\mu = \Delta/\sigma$, and this is tight: if the sensitivity is attained, the trade-off function of some neighbouring pair equals $G_{\Delta/\sigma}$.

## Proof sketch

For neighbours $S, S'$ the outputs are $\mathcal{N}(q(S), \sigma^2 I)$ and $\mathcal{N}(q(S'), \sigma^2 I)$. By rotation invariance, testing between them reduces to testing the projection onto the direction $q(S') - q(S)$, which is a one-dimensional test between $\mathcal{N}(0,1)$ and $\mathcal{N}(\|q(S) - q(S')\|_2/\sigma, 1)$; its trade-off function $G_{\|q(S)-q(S')\|/\sigma}$ is decreasing in the mean gap, hence at least $G_{\Delta/\sigma}$.

## Depends on

- [Gaussian differential privacy](gaussian-differential-privacy.md)

## Sources

- J. Dong, A. Roth, W. J. Su, "Gaussian Differential Privacy", Journal of the Royal Statistical Society Series B 84 (2022), arXiv:1905.02383.
