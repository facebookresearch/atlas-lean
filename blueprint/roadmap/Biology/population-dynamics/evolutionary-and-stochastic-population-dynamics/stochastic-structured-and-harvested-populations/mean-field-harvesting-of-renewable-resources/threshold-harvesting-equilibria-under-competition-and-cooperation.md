# Threshold harvesting equilibria under competition and cooperation

A renewable resource stand (in the Faustmann model, the wood volume of a forest) follows a regular one-dimensional Itô diffusion $dX_t = \mu(X_t)\,dt + \sigma(X_t)\,dW_t$ on $(0,\infty)$. An owner harvests at stopping times $\tau_1 < \tau_2 < \dots$, each harvest resetting the stand to a fixed level $y_0 > 0$ at fixed cost $K > 0$. A *threshold strategy* $R(y)$, $y > y_0$, harvests whenever $X$ reaches $y$; write $\xi(y) = \mathbb{E}_{y_0}[\tau_y]$ for the expected rotation length. A continuum of identical owners sells into one market, and the revenue $\gamma(x, q)$ of a harvest of size $x$ depends on the aggregate harvesting rate $q = (\mathbb{E}[X_{\tau-}] - y_0)/\mathbb{E}[\tau]$ given by renewal theory. Owners maximize the long-term average reward

$$
\liminf_{T\to\infty} \frac1T\, \mathbb{E}_x\Big[\sum_{n : \tau_n \le T} \big(\gamma(X_{\tau_n-}, q) - K\big)\Big] .
$$

**Theorem.** Under the paper's standing assumptions on the diffusion and the price function:

1. (Competition) A mean field equilibrium in threshold strategies exists, and it is unique; call its threshold $y^g$.
2. (Cooperation) The mean field control problem, in which all owners use a common strategy and the market rate is that strategy's own harvesting rate, has value $\sup_y H(y)$ with

$$
H(y) = \frac{\gamma\big(y, \frac{y - y_0}{\xi(y)}\big) - K}{\xi(y)},
$$

and the threshold strategy $R(y^p)$ at a maximizer $y^p$ of $H$ is optimal among stationary strategies.
3. $y^p \ge y^g$: cooperating owners harvest later, at larger stand sizes, than competing ones.

## Expansion

For a fixed market rate the single-owner problem is a classical long-run average impulse control problem, solved by maximizing $(f(y) - K - \text{running cost})/\xi(y)$ over thresholds. The competitive equilibrium is a fixed point of the map from a market rate to the rate induced by the best-response threshold, obtained by continuity and monotonicity. In the cooperative problem each owner internalizes the price effect of the common harvest rate, which, as in a cartel, lowers harvesting intensity and lengthens rotations. When prices depend instead on the mean stationary stand size, the paper shows the order reverses.

## Sources

- Sören Christensen, Berenice Anne Neumann and Tobias Sohr, *Competition versus Cooperation: A class of solvable mean field impulse control problems*, arXiv:2010.06452, Theorems 4.1 and 4.2 (Section 4), Theorem 5.1 (Section 5), Theorem 6.1 (Section 6) and Theorem 7.8 (Section 7). <https://doi.org/10.48550/arXiv.2010.06452> Published version: SIAM Journal on Control and Optimization 59 (2021) 3946–3972, <https://doi.org/10.1137/20m1373372>.
