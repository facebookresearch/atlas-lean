# Approximate zero-concentrated differential privacy

For $\rho \ge 0$ and $\delta \in [0,1]$, a mechanism $M$ is **$\delta$-approximately $\rho$-zCDP** if for every pair of neighbouring datasets $S, S'$ there are events $E, E'$ with $\Pr[M(S) \in E] \ge 1 - \delta$ and $\Pr[M(S') \in E'] \ge 1 - \delta$ such that the conditional output distributions satisfy $D_\alpha\big(M(S) \mid E \,\|\, M(S') \mid E'\big) \le \rho\alpha$ for all $\alpha \in (1, \infty)$. With $\delta = 0$ this is $\rho$-zCDP; approximate zCDP composes additively in both parameters and unifies approximate differential privacy (which is $\delta$-approximately $\varepsilon^2/2$-zCDP when $\varepsilon$-DP holds off an event of probability $\delta$) with concentrated privacy.

## Depends on

- [Zero-concentrated differential privacy](zero-concentrated-dp.md)
- [Differential privacy](../differential-privacy/differentially-private.md)

## Sources

- M. Bun, T. Steinke, "Concentrated Differential Privacy: Simplifications, Extensions, and Lower Bounds", TCC (2016), arXiv:1605.02065.
