# Smooth auctions have bounded price of anarchy; first-price auctions achieve 1 − 1/e

If a mechanism is $(\lambda, \mu)$-smooth with $\mu \ge 1$ and bidding $0$ yields nonnegative utility, then at every pure Nash equilibrium, every correlated equilibrium, and (with independent values) every Bayes–Nash equilibrium, the expected social welfare is at least $\frac{\lambda}{\mu}$ times the optimal expected welfare. The single-item first-price auction is $(\tfrac12, 1)$-smooth via the deviation to half one's value, and with geometric shading grids $(1 - 1/e - \varepsilon, 1)$-smooth for every $\varepsilon > 0$, so its Bayes–Nash equilibria achieve at least a $1 - 1/e$ fraction of optimal welfare.

## Proof sketch

Sum the smoothness inequality over bidders at an equilibrium, use that equilibrium utility is at least the deviation utility and that total utility plus revenue equals welfare. For first price, a bidder with the highest value deviating to a random bid from the density $1/(v - z)$ on $[0, (1 - 1/e) v]$ either wins with high surplus or certifies a high price.

## Depends on

- [Smooth mechanism](smooth-mechanism.md)
- [Bayesian Nash equilibrium](../revelation-principle/is-bayes-nash.md)
- [Correlated equilibrium](../../noncooperative-games/correlated-equilibria/is-correlated-eq.md)

## Sources

- Vasilis Syrgkanis and Eva Tardos, "Composable and Efficient Mechanisms", Proceedings of the 45th Annual ACM Symposium on Theory of Computing (STOC 2013), 2013.
- Tim Roughgarden, "Intrinsic Robustness of the Price of Anarchy", Journal of the ACM, 2015.
- George Christodoulou, Annamaria Kovacs and Michael Schapira, "Bayesian Combinatorial Auctions", Automata, Languages and Programming (ICALP 2008), 2008.
