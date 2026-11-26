# The potential function method bounds the price of stability

Let $G$ be a finite game with social cost $C$ and a generalized ordinal potential $\Phi$ such that $C(s)/A \le \Phi(s) \le B\, C(s)$ for all profiles $s$, with constants $A, B > 0$. Then from every profile $s^0$ some sequence of improving moves reaches a pure Nash equilibrium $s$ with $C(s) \le AB \cdot C(s^0)$; in particular there is a pure Nash equilibrium of cost at most $AB$ times optimal, so the price of stability is at most $AB$.

## Proof sketch

Run improvement dynamics from $s^0$; the potential decreases, so the final equilibrium $s$ has $C(s) \le A \Phi(s) \le A \Phi(s^0) \le AB\, C(s^0)$.

## Depends on

- [Ordinal, generalized ordinal and weighted potentials](ordinal-generalized-ordinal-and-weighted-potentials.md)
- [Price of anarchy and price of stability](../../no-regret-dynamics/remaining-clauses-of-social-cost-price-of-anarchy-and-stabil.md)

## Proof depends on

- [Generalized ordinal potentials give the finite improvement property](generalized-ordinal-potentials-give-the-finite-improvement-property.md)

## Sources

- Eva Tardos and Tom Wexler, "Network Formation Games and the Potential Function Method", Algorithmic Game Theory, Cambridge University Press, 2007.
