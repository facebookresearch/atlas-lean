# The H_k price of stability is tight on directed single-sink networks

For every $k \ge 1$ and every $r < H_k$ there is $\varepsilon > 0$ and a directed single-sink fair connection game on $k + 2$ vertices (zero-cost feeder arcs from each source to a hub, a shared trunk of cost $1 + \varepsilon$ from the hub to the sink, and a private bypass of cost $1/i$ for source $i$) whose unique pure Nash equilibrium costs more than $r$ times the optimum. At $\varepsilon = 0$ both the all-bypass profile (cost $H_k$) and the all-trunk profile (cost $1$) are pure Nash equilibria. In the undirected counterpart of this network the price of stability is $1$: routing every player through the cheapest bypass and the shared edge to the sink is a socially optimal pure Nash equilibrium.

## Proof sketch

With $\varepsilon > 0$, if $j$ players use the trunk then the last of them pays $(1 + \varepsilon)/j > 1/j$, so it prefers its bypass; inductively all players defect to their bypasses, giving cost $H_k$ against the optimum $1 + \varepsilon$.

## Depends on

- [Fair connection game on a network](fair-connection-game-on-a-network.md)
- [Price of anarchy and price of stability](../../no-regret-dynamics/remaining-clauses-of-social-cost-price-of-anarchy-and-stabil.md)

## Proof depends on

- [Price of stability of fair cost sharing is at most H(k)](../../potential-games/exists-is-pure-nash-network-cost-le.md)

## Sources

- Elliot Anshelevich et al., "The Price of Stability for Network Design with Fair Cost Allocation", SIAM Journal on Computing, 2008.
- Tim Roughgarden and Eva Tardos, "Introduction to the Inefficiency of Equilibria", Algorithmic Game Theory, Cambridge University Press, 2007.
- Eva Tardos and Tom Wexler, "Network Formation Games and the Potential Function Method", Algorithmic Game Theory, Cambridge University Press, 2007.
