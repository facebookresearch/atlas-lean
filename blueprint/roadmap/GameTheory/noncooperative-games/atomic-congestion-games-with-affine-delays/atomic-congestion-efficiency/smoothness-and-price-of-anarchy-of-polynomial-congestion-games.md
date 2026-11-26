# Smoothness and price of anarchy of polynomial congestion games

Let $d \ge 1$ and let $\varphi_d > 1$ be the unique root of $\varphi^{d+1} = (1 + \varphi)^d$. Every atomic congestion game whose resource latencies are polynomials $\ell_e(k) = \sum_{j=0}^d a_{e,j} k^j$ with nonnegative coefficients is $(\lambda_d, \mu_d)$-smooth for some $\lambda_d > 0$ and $\mu_d \in [0, 1)$ with $\lambda_d / (1 - \mu_d) = \varphi_d^{\,d+1}$. Consequently every pure Nash equilibrium, and in expectation every coarse correlated equilibrium, has social cost at most $\varphi_d^{\,d+1}$ times the cost of any profile, and in particular at most $(d+1)^{d+1}$ times it.

## Proof sketch

For reals $y, z \ge 0$ prove $y (z+y)^j \le \lambda_d y^{j+1} + \mu_d z^{j+1}$ for every $j \le d$ by optimizing the ratio, with the extremal ratio attained where $\varphi^{d+1} = (1+\varphi)^d$; since $(z+1)^j \le (z+y)^j$ for natural $y \ge 1$, this gives $y (z+1)^j \le \lambda_d y^{j+1} + \mu_d z^{j+1}$ for natural $y, z$. Summing over resources gives smoothness, and the robust price-of-anarchy theorem gives the bounds.

## Depends on

- [Congestion game](../../potential-games/congestion-game.md)
- [Smooth game](../../no-regret-dynamics/is-smooth.md)

## Proof depends on

- [Extension theorem for coarse correlated equilibria](../../no-regret-dynamics/expected-social-cost-le.md)

## Sources

- Baruch Awerbuch, Yossi Azar and Amir Epstein, "The Price of Routing Unsplittable Flow", Proceedings of the 37th Annual ACM Symposium on Theory of Computing, 2005.
- Sebastian Aland et al., "Exact Price of Anarchy for Polynomial Congestion Games", Proceedings of the 23rd Annual Symposium on Theoretical Aspects of Computer Science (STACS 2006), 2006.
- Tim Roughgarden, "Intrinsic Robustness of the Price of Anarchy", Journal of the ACM, 2015.
