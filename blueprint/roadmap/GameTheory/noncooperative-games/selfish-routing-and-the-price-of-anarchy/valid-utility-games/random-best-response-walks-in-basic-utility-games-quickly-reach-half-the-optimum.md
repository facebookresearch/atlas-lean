# Random best-response walks in basic utility games quickly reach half the optimum

Let a monotone basic utility game have $n \ge 1$ players and $V(\emptyset) \ge 0$. Consider the walk in which at each step a uniformly random player switches to a best response. From any starting profile, after $t \ge \frac n2 \ln(1/\varepsilon)$ steps the expected social value is at least $(\tfrac12 - \varepsilon)\, V(o)$ for every profile $o$ and every $\varepsilon > 0$.

## Proof sketch

The expected one-step gain of a random best response is at least $\frac1n (V(o) - 2V(s))$ by the same submodularity chain as in the price-of-anarchy proof; the gap $V(o) - 2V(s)$ therefore contracts by a factor $1 - 2/n$ in expectation per step.

## Depends on

- [Valid and basic utility games](valid-and-basic-utility-games.md)

## Proof depends on

- [Basic utility games are exact potential games with price of stability 1](basic-utility-games-are-exact-potential-games-with-price-of-stability-1.md)
- [Price of anarchy at most 2 for monotone valid utility games](price-of-anarchy-at-most-2-for-monotone-valid-utility-games.md)

## Sources

- Eva Tardos and Tom Wexler, "Network Formation Games and the Potential Function Method", Algorithmic Game Theory, Cambridge University Press, 2007.
- Vahab S. Mirrokni and Adrian Vetta, "Convergence Issues in Competitive Games", Approximation, Randomization, and Combinatorial Optimization: Algorithms and Techniques (APPROX/RANDOM 2004), 2004.
- Michel X. Goemans, Vahab S. Mirrokni and Adrian Vetta, "Sink Equilibria and Convergence", 46th Annual IEEE Symposium on Foundations of Computer Science (FOCS 2005), 2005.
