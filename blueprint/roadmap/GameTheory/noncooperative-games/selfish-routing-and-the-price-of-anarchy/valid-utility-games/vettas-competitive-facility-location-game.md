# Vetta's competitive facility location game

Providers $i$ choose locations $s_i$ from finite sets; clients $j$ have reservation values $\pi_j$ and connection costs $c_j(\ell) \le \pi_j$ to locations $\ell$ (as in the sources: lowering a larger cost to $\pi_j$ changes no social value). Each client is served by its cheapest provider at a price equal to the second-cheapest connection cost capped at $\pi_j$ (the price is $\pi_j$ if there is no other provider), so provider $i$ earns from client $j$ the difference between that price and its own connection cost when it is cheapest. The social welfare of a profile is $\sum_j (\pi_j - \min(\pi_j, \min_i c_j(s_i)))$.

## Depends on

- [Valid and basic utility games](valid-and-basic-utility-games.md)

## Sources

- Eva Tardos and Tom Wexler, "Network Formation Games and the Potential Function Method", Algorithmic Game Theory, Cambridge University Press, 2007.
- Adrian Vetta, "Nash Equilibria in Competitive Societies, with Applications to Facility Location, Traffic Routing and Auctions", 43rd Annual IEEE Symposium on Foundations of Computer Science (FOCS 2002), 2002.
