# Zero-concentrated differential privacy

Datasets are elements of $\mathcal{X}^n$; two datasets are neighbours if they differ in exactly one entry; a mechanism $M$ maps a dataset to a random output. For distributions $P, Q$ and $\alpha \in (1, \infty)$ the Rényi divergence is $D_\alpha(P \| Q) = \frac{1}{\alpha - 1}\log \int \big(\frac{dP}{dQ}\big)^{\alpha} dQ$ (and $+\infty$ if $P \not\ll Q$). For $\rho \ge 0$, a mechanism $M$ is **$\rho$-zero-concentrated differentially private** ($\rho$-zCDP) if

$$
D_\alpha\big(M(S) \,\|\, M(S')\big) \le \rho\,\alpha \quad \text{for all neighbouring } S, S' \text{ and all } \alpha \in (1, \infty).
$$

Equivalently, the privacy loss random variable is sub-Gaussian with mean at most $\rho$ in the sense of its moment generating function. Unlike approximate differential privacy, zCDP has no additive failure probability; it lies strictly between pure and approximate differential privacy.

## Depends on

- [Differential privacy](../differential-privacy/differentially-private.md)
- [Rényi differential privacy of the Gaussian mechanism](../differential-privacy/renyi-differential-privacy-of-the-gaussian.md)

## Sources

- M. Bun, T. Steinke, "Concentrated Differential Privacy: Simplifications, Extensions, and Lower Bounds", TCC (2016), arXiv:1605.02065.
