# Projected discrete tâtonnement computes approximate equilibria of WGS markets

Let an exchange market with $n$ goods satisfy the standing assumptions of Codenotti and Varadarajan (concave, monotone, nonsatiable utilities, every trader endowed with some good, single-valued demand), and let its excess demand satisfy weak gross substitutability. Rescale units so that every good has total supply $1$ and, for a parameter $0 < \eta \le 1$, add a phantom trader with endowment $\eta$ of every good and Cobb–Douglas utility $\prod_j x_j^{1/n}$; the resulting market $\hat M$, with excess demand $Z$, satisfies WGS and has an equilibrium in the box $\Delta = \{\pi : \eta/(2n) \le \pi_j \le 1\}$. The discrete tâtonnement process starts at any $\pi^0 \in \Delta$; if $\pi^{t}$ lies outside the box $\Delta^+ = \{\pi : \eta/(4n) \le \pi_j \le 1 + \eta/(4n)\}$, then $\pi^{t+1}$ is the point of $\Delta$ closest to $\pi^t$, and otherwise $\pi^{t+1} = \pi^t + \delta\,(12n^2/\eta)^{-2}\, Z(\pi^t)$, where $\delta > 0$, with $1/\delta$ polynomial in $n$, $1/\varepsilon$ and $1/\eta$, is a lower bound on $\pi^* \cdot Z(\pi)$ for an equilibrium $\pi^* \in \Delta$ and every $\pi \in \Delta^+$ that is not a weak $(1+\varepsilon)$-approximate equilibrium (such a $\delta$ exists by the separating-hyperplane property under WGS). Within a number of iterations polynomial in $n$, $1/\varepsilon$ and $1/\eta$, some iterate in $\Delta^+$ is a weak $(1+\varepsilon)$-approximate equilibrium of $\hat M$: there are bundles that are $(1+\varepsilon)$-approximate demands (utility at least $1/(1+\varepsilon)$ times the optimum over the budget set, and cost at most $(1+\varepsilon)$ times the trader's income) whose total amount of every good is at most $(1+\varepsilon)$ times its supply. With $\eta = \varepsilon$ (for $0 < \varepsilon \le 1$) and the units rescaled back, this price is a weak $(1+\varepsilon)^2$-approximate equilibrium of the original market, reached after a number of iterations polynomial in $1/\varepsilon$ and in the size of the market.

## Proof sketch

The phantom trader keeps the regularized market WGS and confines equilibria to the box. For a fixed equilibrium $\pi^* \in \Delta$, the separating-hyperplane property $\pi^* \cdot Z(\pi) \ge \delta$ at every $\pi \in \Delta^+$ that is not a weak $(1+\varepsilon)$-approximate equilibrium, together with $\|Z(\pi)\|_2 \le 12n^2/\eta$ on $\Delta^+$, makes $\|\pi^* - \pi^t\|^2$ drop by at least $\min\bigl(\delta^2/(12n^2/\eta)^2, (\eta/(4n))^2\bigr)$ at every step until such a point is reached; since $\|\pi^* - \pi^0\|^2 \le n$, this bounds the number of iterations.

## Depends on

- [Gross substitutability of an excess-demand function](gross-substitutability-of-an-excess-demand-function.md)
- [Arrow–Debreu exchange market and competitive equilibrium](../exchange-economies/arrow-debreu-exchange-market-and-competitive-equilibrium.md)

## Proof depends on

- [Uniqueness and convexity of equilibria under gross substitutability](uniqueness-and-convexity-of-equilibria-under-gross-substitutability.md)

## Sources

- Bruno Codenotti, Benton McCune and Kasturi Varadarajan, "Market Equilibrium via the Excess Demand Function", Proceedings of the Thirty-Seventh Annual ACM Symposium on Theory of Computing (STOC '05), 2005.
- Bruno Codenotti and Kasturi Varadarajan, "Computation of Market Equilibria by Convex Programming", Algorithmic Game Theory, Cambridge University Press, 2007.
