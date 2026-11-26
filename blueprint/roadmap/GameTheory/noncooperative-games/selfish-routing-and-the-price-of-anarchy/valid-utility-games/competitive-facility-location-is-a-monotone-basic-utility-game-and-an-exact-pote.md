# Competitive facility location is a monotone basic utility game and an exact potential game

In Vetta's competitive facility location game, social welfare is a monotone submodular function of the set of opened locations, total provider profit is at most social welfare, and each provider's profit equals its marginal contribution $V(s) - V(s - s_i)$. Hence the game is a monotone basic utility game, negative social welfare is an exact potential, pure Nash equilibria exist, every welfare-maximizing profile is an equilibrium (price of stability $1$), improvement dynamics terminate, and every pure Nash equilibrium has welfare at least half the optimum; an instance with two providers and two clients shows the factor $2$ is attained.

## Proof sketch

For each client the welfare is $\pi_j$ minus the minimum capped connection cost, a monotone submodular function of the set of locations; second-price profits telescope into marginal contributions.

## Depends on

- [Vetta's competitive facility location game](vettas-competitive-facility-location-game.md)

## Proof depends on

- [Basic utility games are exact potential games with price of stability 1](basic-utility-games-are-exact-potential-games-with-price-of-stability-1.md)
- [Price of anarchy at most 2 for monotone valid utility games](price-of-anarchy-at-most-2-for-monotone-valid-utility-games.md)

## Sources

- Eva Tardos and Tom Wexler, "Network Formation Games and the Potential Function Method", Algorithmic Game Theory, Cambridge University Press, 2007.
- Adrian Vetta, "Nash Equilibria in Competitive Societies, with Applications to Facility Location, Traffic Routing and Auctions", 43rd Annual IEEE Symposium on Foundations of Computer Science (FOCS 2002), 2002.
