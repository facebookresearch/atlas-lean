# Dalang–Morton–Willinger theorem

Let $(\Omega, \mathcal F, (\mathcal F_t)_{t=0}^T, \mathbb P)$ be a filtered probability space with finite horizon $T \in \mathbb N$, and $S = (S_t)_{t=0}^T$ an adapted process in $\mathbb R^d$ of discounted asset prices. A self-financing strategy is a predictable process $H = (H_t)_{t=1}^T$ in $\mathbb R^d$, with gains $G_T(H) = \sum_{t=1}^T H_t \cdot (S_t - S_{t-1})$; an arbitrage is an $H$ with $G_T(H) \ge 0$ almost surely and $\mathbb P(G_T(H) > 0) > 0$. Then there is no arbitrage if and only if there is a probability measure $Q \sim \mathbb P$ with bounded density $dQ/d\mathbb P$ under which $S$ is a martingale. No finiteness of $\Omega$ is assumed. The multi-period statement reduces to the [conditional one-period theorem](conditional-one-period-ftap.md): no arbitrage holds if and only if there is no arbitrage given $\mathcal F_{t-1}$ for each increment $S_t - S_{t-1}$, and the one-period densities $Z_t$ multiply to $dQ/d\mathbb P = \prod_{t=1}^T Z_t$. The one-asset case $d = 1$ is the special case in which the conditional theorem reduces to a sign condition on the conditional law of the increment.

## Depends on

- [Conditional one-period fundamental theorem of asset pricing](conditional-one-period-ftap.md)

## Expansion

This page becomes ready once:

- the equivalence of global and one-period no arbitrage, and the pasting of the conditional densities, are stated (proof prerequisite; not yet stated)

## Sources

- R. C. Dalang, A. Morton and W. Willinger, "Equivalent martingale measures and no-arbitrage in stochastic securities market models", *Stochastics and Stochastic Reports* 29(2):185–201, 1990
- H. Föllmer and A. Schied, *Stochastic Finance: An Introduction in Discrete Time*, de Gruyter, Section 5.2 (the Dalang–Morton–Willinger theorem)
