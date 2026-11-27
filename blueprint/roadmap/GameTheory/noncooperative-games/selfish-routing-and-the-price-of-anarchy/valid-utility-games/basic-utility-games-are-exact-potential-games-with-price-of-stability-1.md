# Basic utility games are exact potential games with price of stability 1

In a basic utility game the social value $V$ is an exact potential (for utilities, which players maximize). Hence finite basic utility games have the finite improvement property, every profile maximizing $V$ is a pure Nash equilibrium, and some pure Nash equilibrium maximizes social value.

## Proof sketch

For a unilateral change of $s_i$, $u_i$ changes by $V(s') - V(s' - s_i') - V(s) + V(s - s_i)$, and $s - s_i = s' - s'_i$, so this equals $V(s') - V(s)$.

## Depends on

- [Valid and basic utility games](valid-and-basic-utility-games.md)
- [Exact potential](../../potential-games/is-exact-potential.md)

## Proof depends on

- [Generalized ordinal potentials give the finite improvement property](../../potential-games/potential-game-characterizations/generalized-ordinal-potentials-give-the-finite-improvement-property.md)

## Sources

- Eva Tardos and Tom Wexler, "Network Formation Games and the Potential Function Method", Algorithmic Game Theory, Cambridge University Press, 2007.
- Adrian Vetta, "Nash Equilibria in Competitive Societies, with Applications to Facility Location, Traffic Routing and Auctions", 43rd Annual IEEE Symposium on Foundations of Computer Science (FOCS 2002), 2002.
