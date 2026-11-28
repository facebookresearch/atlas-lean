# Gaussian differential privacy

For $\mu \ge 0$ let $G_\mu = T\big(\mathcal{N}(0,1), \mathcal{N}(\mu,1)\big)$, explicitly

$$
G_\mu(\alpha) = \Phi\big(\Phi^{-1}(1 - \alpha) - \mu\big), \qquad \alpha \in [0,1],
$$

where $\Phi$ is the standard normal distribution function. A mechanism is **$\mu$-Gaussian differentially private** ($\mu$-GDP) if it is $G_\mu$-DP. Thus $\mu$-GDP means that distinguishing neighbouring datasets from the output is at least as hard as distinguishing two unit-variance Gaussians whose means are $\mu$ apart; $G_0(\alpha) = 1 - \alpha$ is perfect privacy and $G_\infty \equiv 0$ is no privacy.

## Depends on

- [f-differential privacy](f-differential-privacy.md)

## Sources

- J. Dong, A. Roth, W. J. Su, "Gaussian Differential Privacy", Journal of the Royal Statistical Society Series B 84 (2022), arXiv:1905.02383.
