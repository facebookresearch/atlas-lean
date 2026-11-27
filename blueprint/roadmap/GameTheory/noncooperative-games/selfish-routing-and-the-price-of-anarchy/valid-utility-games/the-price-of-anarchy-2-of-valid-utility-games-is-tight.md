# The price of anarchy 2 of valid utility games is tight

The closed-neighbourhood location game on a finite undirected graph, in which each player selects a vertex, each vertex $v$ splits one unit of value equally among the players located in its closed neighbourhood $N[v]$, and the social value is the number of vertices with at least one player in their closed neighbourhood, is a valid utility game. For every $\varepsilon > 0$ there is a graph and a pure Nash equilibrium $s$ of positive welfare with a profile $o$ satisfying $(2 - \varepsilon) V(s) < V(o)$.

## Proof sketch

Use a star-like graph where all players crowd a central vertex in equilibrium while the optimum spreads them over many leaves of equal value.

## Depends on

- [Valid and basic utility games](valid-and-basic-utility-games.md)

## Proof depends on

- [Price of anarchy at most 2 for monotone valid utility games](price-of-anarchy-at-most-2-for-monotone-valid-utility-games.md)

## Sources

- Eva Tardos and Tom Wexler, "Network Formation Games and the Potential Function Method", Algorithmic Game Theory, Cambridge University Press, 2007, Exercise 19.16 (part (a): the price of anarchy of this location game can be arbitrarily close to $2$; part (b): it is a valid utility game).
