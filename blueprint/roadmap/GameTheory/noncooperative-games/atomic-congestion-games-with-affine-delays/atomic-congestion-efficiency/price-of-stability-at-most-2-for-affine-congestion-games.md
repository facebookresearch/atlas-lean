# Price of stability at most 2 for affine congestion games

In an atomic congestion game with nondecreasing latencies, Rosenthal's potential satisfies $\Phi(s) \le C(s)$. If the latencies are nonnegative affine functions $\ell_e(k) = a_e k + b_e$, then also $C(s) \le 2\Phi(s)$. Consequently from every profile some improvement path reaches a pure Nash equilibrium of social cost at most twice the starting cost, and the price of stability of affine congestion games is at most $2$.

## Proof sketch

Each resource with load $n$ contributes $\sum_{k \le n} \ell_e(k)$ to $\Phi$, which lies between $n \ell_e(n)/2$ and $n \ell_e(n)$ for affine nonnegative latencies. Apply the potential function method with $A = 2$, $B = 1$ for the price of stability. For the improvement-path clause, an improving move of a player lowers that player's cost and hence, $\Phi$ being an exact potential, strictly lowers $\Phi$; since there are finitely many profiles, every sequence of improving moves from $s^0$ is finite and ends at a pure Nash equilibrium $s$ with $\Phi(s) \le \Phi(s^0)$, so $C(s) \le 2\Phi(s) \le 2\Phi(s^0) \le 2C(s^0)$.

## Depends on

- [Congestion game](../../potential-games/congestion-game.md)
- [Rosenthal's theorem](../../potential-games/is-exact-potential-potential.md)
- [Price of anarchy and price of stability](../../no-regret-dynamics/remaining-clauses-of-social-cost-price-of-anarchy-and-stabil.md)

## Proof depends on

- [The potential function method bounds the price of stability](../../potential-games/potential-game-characterizations/the-potential-function-method-bounds-the-price-of-stability.md)

## Sources

- Tim Roughgarden, "CS364A: Algorithmic Game Theory, Lecture Notes", Stanford University, Fall 2013, 2013.
- Eva Tardos and Tom Wexler, "Network Formation Games and the Potential Function Method", Algorithmic Game Theory, Cambridge University Press, 2007.
