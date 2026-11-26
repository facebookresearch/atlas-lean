# Price of anarchy at most 2 for monotone valid utility games

In a monotone valid utility game, every pure Nash equilibrium $s$ satisfies $V(o) \le 2 V(s)$ for every profile $o$, and the same factor-$2$ bound holds in expectation for every mixed Nash equilibrium and every coarse correlated equilibrium.

## Proof sketch

By monotonicity and submodularity, $V(o) - V(s) \le \sum_i [V(s + o_i) - V(s)] \le \sum_i [V(s - s_i + o_i) - V(s - s_i)] \le \sum_i u_i(o_i, s_{-i}) \le \sum_i u_i(s) \le V(s)$, using the validity conditions and the equilibrium inequalities.

## Depends on

- [Valid and basic utility games](valid-and-basic-utility-games.md)
- [Coarse correlated equilibrium](../../no-regret-dynamics/is-coarse-correlated-eq.md)

## Sources

- Eva Tardos and Tom Wexler, "Network Formation Games and the Potential Function Method", Algorithmic Game Theory, Cambridge University Press, 2007.
- Adrian Vetta, "Nash Equilibria in Competitive Societies, with Applications to Facility Location, Traffic Routing and Auctions", 43rd Annual IEEE Symposium on Foundations of Computer Science (FOCS 2002), 2002.
