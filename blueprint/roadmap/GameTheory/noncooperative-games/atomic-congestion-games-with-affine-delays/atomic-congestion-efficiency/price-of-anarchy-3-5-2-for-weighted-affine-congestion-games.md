# Price of anarchy (3 + √5)/2 for weighted affine congestion games

Every weighted atomic congestion game with nonnegative weights and nonnegative affine latencies is smooth with ratio $\varphi^2 = (3 + \sqrt5)/2 \approx 2.618$. Hence every pure Nash equilibrium, and in expectation every mixed Nash and coarse correlated equilibrium, has social cost at most $(3 + \sqrt5)/2$ times the optimum. The bound is tight: it is attained by a weighted variant of the four-player example of Awerbuch, Azar and Epstein (AGT, Example 18.6 and Exercise 18.2(a)), whereas the unweighted bound is $5/2$.

## Proof sketch

An elementary inequality $z(y + z) \le \lambda z^2 + \mu y^2$ for reals $y, z \ge 0$, with $\mu < 1$ and $\lambda/(1-\mu) = (3+\sqrt5)/2$, applied to weighted loads and summed over resources gives smoothness. The tight instance reweights the four players of the Awerbuch–Azar–Epstein triangle example, whose unweighted price of anarchy is $5/2$.

## Depends on

- [Weighted atomic congestion game](weighted-atomic-congestion-game.md)
- [Smooth game](../../no-regret-dynamics/is-smooth.md)

## Proof depends on

- [Extension theorem for coarse correlated equilibria](../../no-regret-dynamics/expected-social-cost-le.md)

## Sources

- Baruch Awerbuch, Yossi Azar and Amir Epstein, "The Price of Routing Unsplittable Flow", Proceedings of the 37th Annual ACM Symposium on Theory of Computing, 2005.
- Noam Nisan, Tim Roughgarden, Eva Tardos and Vijay V. Vazirani, "Algorithmic Game Theory", Cambridge University Press, 2007.
