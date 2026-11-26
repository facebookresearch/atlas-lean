# Projected discrete tâtonnement computes approximate equilibria of WGS markets

For an exchange market whose excess demand satisfies weak gross substitutability, after rescaling units and adding a phantom trader that regularizes demand on a bounded price box, the projected discrete tâtonnement process $p^{t+1}_g = \Pi\bigl(p^t_g (1 + \delta Z_g(p^t))\bigr)$, with a suitably small step $\delta$ and projection $\Pi$ onto the box, reaches a weak approximate equilibrium: a price vector at which every good's excess demand is at most an $\varepsilon$ fraction of supply, after a number of iterations bounded explicitly in terms of the market parameters and $1/\varepsilon$.

## Proof sketch

The phantom trader keeps the regularized market WGS and confines equilibria to the box. The separating-hyperplane property makes the distance to the equilibrium set decrease by a fixed amount at every step at which the current prices are not approximately clearing.

## Depends on

- [Gross substitutability of an excess-demand function](gross-substitutability-of-an-excess-demand-function.md)

## Proof depends on

- [Uniqueness and convexity of equilibria under gross substitutability](uniqueness-and-convexity-of-equilibria-under-gross-substitutability.md)

## Sources

- Bruno Codenotti, Benton McCune and Kasturi Varadarajan, "Market Equilibrium via the Excess Demand Function", Proceedings of the Thirty-Seventh Annual ACM Symposium on Theory of Computing (STOC '05), 2005.
- Bruno Codenotti and Kasturi Varadarajan, "Computation of Market Equilibria by Convex Programming", Algorithmic Game Theory, Cambridge University Press, 2007.
