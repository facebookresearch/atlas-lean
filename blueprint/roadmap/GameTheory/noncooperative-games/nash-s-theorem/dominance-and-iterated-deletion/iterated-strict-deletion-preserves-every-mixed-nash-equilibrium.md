# Iterated strict deletion preserves every mixed Nash equilibrium

Let $G$ be a finite game and $R^\infty$ its iterated strict-deletion limit. Every mixed Nash equilibrium of $G$ is supported in $R^\infty$, and a mixed profile supported in $R^\infty$ is a Nash equilibrium of $G$ if and only if it is a Nash equilibrium of the restriction of $G$ to $R^\infty$.

## Proof sketch

By induction on rounds: an equilibrium supported in $R^k$ is an equilibrium of the restricted game, so it gives zero weight to strategies dominated relative to $R^k$. A strategy deleted at some stage is dominated against all surviving opponent profiles, hence also against the equilibrium mixture, so restoring deleted strategies creates no profitable deviation.

## Depends on

- [Iterated deletion of strictly dominated strategies](iterated-deletion-of-strictly-dominated-strategies.md)
- [Mixed Nash equilibrium](../is-mixed-nash.md)

## Proof depends on

- [Mixed Nash equilibria put zero weight on strictly dominated strategies](mixed-nash-equilibria-put-zero-weight-on-strictly-dominated-strategies.md)

## Sources

- Eva Tardos and Vijay V. Vazirani, "Basic Solution Concepts and Computational Issues", Algorithmic Game Theory, Cambridge University Press, 2007.
- Noam Nisan, Tim Roughgarden, Eva Tardos and Vijay V. Vazirani, "Algorithmic Game Theory", Cambridge University Press, 2007.
