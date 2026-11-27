# The potential function method bounds the price of stability

Let $G$ be a finite cost game with social cost $C$ and an exact potential $\Phi$ such that $C(s)/A \le \Phi(s) \le B\, C(s)$ for all profiles $s$, with constants $A, B > 0$. Then every profile minimizing $\Phi$ is a pure Nash equilibrium $s$ with $C(s) \le AB \cdot C(s^*)$ for every profile $s^*$; in particular the price of stability is at most $AB$.

## Proof sketch

A minimizer $s$ of $\Phi$ is a pure Nash equilibrium, and for every profile $s^*$ we get $C(s) \le A \Phi(s) \le A \Phi(s^*) \le AB\, C(s^*)$.

## Depends on

- [Exact potential](../is-exact-potential.md)
- [Price of anarchy and price of stability](../../no-regret-dynamics/remaining-clauses-of-social-cost-price-of-anarchy-and-stabil.md)

## Proof depends on

- [Potential minimisers are Nash equilibria](../is-pure-nash-of-forall-le.md)

## Sources

- Eva Tardos and Tom Wexler, "Network Formation Games and the Potential Function Method", Algorithmic Game Theory, Cambridge University Press, 2007, Theorem 19.13 and its proof (a strategy vector minimizing the potential is a Nash equilibrium of cost at most $AB$ times the minimum cost).
