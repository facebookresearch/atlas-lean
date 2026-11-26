# The Delbaen–Schachermayer fundamental theorem of asset pricing

Let $S$ be a locally bounded $\mathbb R^d$-valued semimartingale on a filtered probability space $(\Omega, \mathcal F, (\mathcal F_t)_{t \in [0, T]}, \mathbb P)$ satisfying the usual conditions, modelling discounted prices. A strategy $H$ is *admissible* if it is predictable and $S$-integrable and the stochastic integral $H \cdot S$ is bounded below by a constant. Let $K = \{(H \cdot S)_T : H \text{ admissible}\}$ and $C = (K - L^0_+) \cap L^\infty$. The market satisfies *no free lunch with vanishing risk* (NFLVR) if the closure of $C$ in the norm of $L^\infty$ meets $L^\infty_+$ only in $0$. Then NFLVR holds if and only if there is a probability measure $Q \sim \mathbb P$ under which $S$ is a local martingale. In discrete time with finitely many states it reduces to the [funded fundamental theorem of asset pricing](../../../Economics/asset-pricing-and-financial-risk/part-01/fundamental-theorem-of-asset-pricing-and-state-p/funded-ftap.md).

## Expansion

This page becomes ready once:

- semimartingales, the stochastic integral $H \cdot S$ and local martingales are stated as prerequisites (statement prerequisite)

## Sources

- F. Delbaen and W. Schachermayer, "A general version of the fundamental theorem of asset pricing", *Mathematische Annalen* 300(3):463–520, 1994
