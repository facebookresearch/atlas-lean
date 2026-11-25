# Dalang–Morton–Willinger theorem

Let $(\Omega, \mathcal F, (\mathcal F_t)_{t=0}^T, \mathbb P)$ be a filtered probability space with finite horizon $T \in \mathbb N$, and $S = (S_t)_{t=0}^T$ an adapted process in $\mathbb R^d$ of discounted asset prices. A self-financing strategy is a predictable process $H = (H_t)_{t=1}^T$ in $\mathbb R^d$, with gains $G_T(H) = \sum_{t=1}^T H_t \cdot (S_t - S_{t-1})$; an arbitrage is an $H$ with $G_T(H) \ge 0$ almost surely and $\mathbb P(G_T(H) > 0) > 0$. Then there is no arbitrage if and only if there is a probability measure $Q \sim \mathbb P$ with bounded density $dQ/d\mathbb P$ under which $S$ is a martingale. No finiteness of $\Omega$ is assumed. The multi-period statement reduces to the [conditional one-period theorem](conditional-one-period-ftap.md): no arbitrage holds if and only if there is no arbitrage given $\mathcal F_{t-1}$ for each increment $S_t - S_{t-1}$. No integrability of the prices under $\mathbb P$ is assumed, so the construction first passes to the equivalent measure $\tilde{\mathbb P}$ with bounded density $d\tilde{\mathbb P}/d\mathbb P = c\, \exp\bigl(-\sum_{t=0}^T |S_t|\bigr)$, $c$ the normalizing constant, under which every $S_t$ is integrable; without this step a bounded density need not make $S$ integrable, as when $S_1 = S_0$ with $S_0$ not integrable. A martingale measure is then built backwards in time from $\tilde{\mathbb P}$: at each step the one-period theorem, applied under the measure already constructed for the later steps, gives a bounded density, and the product of $d\tilde{\mathbb P}/d\mathbb P$ and these bounded densities, normalized to have expectation $1$, is a bounded density $dQ/d\mathbb P$ under which every $S_t$ is integrable and $S$ is a martingale. The one-asset case $d = 1$ is the special case in which the conditional theorem reduces to a sign condition on the conditional law of the increment.

## Depends on

- [Conditional one-period fundamental theorem of asset pricing](conditional-one-period-ftap.md)

## Expansion

This page becomes ready once:

- the equivalence of global and one-period no arbitrage, the preliminary change to a measure under which the prices are integrable, and the backward construction of the bounded density, are stated (proof prerequisite)

## Sources

- R. C. Dalang, A. Morton and W. Willinger, "Equivalent martingale measures and no-arbitrage in stochastic securities market models", *Stochastics and Stochastic Reports* 29(2):185–201, 1990
- H. Föllmer and A. Schied, *Stochastic Finance: An Introduction in Discrete Time*, de Gruyter, Section 5.2 (the Dalang–Morton–Willinger theorem)
- Yu. M. Kabanov and C. Stricker, "A teachers' note on no-arbitrage criteria", in *Séminaire de Probabilités XXXV*, Lecture Notes in Mathematics 1755, Springer, 2001, pp. 149–152, Theorem 1
