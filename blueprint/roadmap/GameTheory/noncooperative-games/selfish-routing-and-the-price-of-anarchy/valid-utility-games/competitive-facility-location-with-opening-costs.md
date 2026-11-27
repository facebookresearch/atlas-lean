# Competitive facility location with opening costs

If providers pay nonnegative opening costs $f(i, s_i)$ and net welfare is $V_f(s) = V(s) - \sum_i f(i, s_i)$, then for every constant $C$ there is an instance with two providers and one client with a pure Nash equilibrium $s$ of positive net welfare and a profile $o$ with $C\, V_f(s) < V_f(o)$, so the price of anarchy is unbounded. Nevertheless every pure Nash equilibrium satisfies $V_f(o) \le 2 V_f(s) + \sum_i f(i, s_i)$.

## Proof sketch

The factor-two argument applies to gross welfare; subtracting the equilibrium opening costs gives the additive bound, while a cheap-to-open but nearly useless incumbent shows unboundedness.

## Depends on

- [Vetta's competitive facility location game](vettas-competitive-facility-location-game.md)

## Proof depends on

- [Price of anarchy at most 2 for monotone valid utility games](price-of-anarchy-at-most-2-for-monotone-valid-utility-games.md)

## Sources

- Eva Tardos and Tom Wexler, "Network Formation Games and the Potential Function Method", Algorithmic Game Theory, Cambridge University Press, 2007.
