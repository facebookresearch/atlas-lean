# Zero-concentrated differential privacy

Datasets are elements of $\mathcal{X}^n$; two datasets are neighbours if they differ in exactly one entry; a mechanism $M$ maps a dataset to a random output. For distributions $P, Q$ and $\alpha \in (1, \infty)$ the Rényi divergence is $D_\alpha(P \| Q) = \frac{1}{\alpha - 1}\log \int \big(\frac{dP}{dQ}\big)^{\alpha} dQ$ (and $+\infty$ if $P \not\ll Q$). For $\rho \ge 0$, a mechanism $M$ is **$\rho$-zero-concentrated differentially private** ($\rho$-zCDP) if

$$
D_\alpha\big(M(S) \,\|\, M(S')\big) \le \rho\,\alpha \quad \text{for all neighbouring } S, S' \text{ and all } \alpha \in (1, \infty).
$$

Equivalently, the privacy loss random variable $Z = \log\frac{dM(S)}{dM(S')}(Y)$, $Y \sim M(S)$, satisfies $\mathbb{E}[e^{(\alpha - 1)Z}] \le e^{(\alpha - 1)\alpha\rho}$ for all $\alpha > 1$, the moment bound of a Gaussian with mean $\rho$ and variance $2\rho$ on that one-sided range (a sub-Gaussian-type condition, not a full two-sided sub-Gaussian bound). Unlike approximate differential privacy, zCDP has no additive failure probability; it lies strictly between pure and approximate differential privacy.

## Depends on

- [Differential privacy](../../differential-privacy/differentially-private.md)

## Sources

- M. Bun, T. Steinke, "Concentrated Differential Privacy: Simplifications, Extensions, and Lower Bounds", TCC (2016), arXiv:1605.02065, Definitions 1.1, 1.2 and 2.1.
