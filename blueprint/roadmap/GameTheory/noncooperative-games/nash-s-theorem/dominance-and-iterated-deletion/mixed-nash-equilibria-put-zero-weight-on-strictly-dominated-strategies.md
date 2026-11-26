# Mixed Nash equilibria put zero weight on strictly dominated strategies

Let $x$ be a mixed Nash equilibrium of a finite cost-minimization game. If the pure strategy $a \in S_i$ is strictly dominated (by a pure or mixed strategy of player $i$), then $x_i(a) = 0$.

## Proof sketch

Against the opponents' mixture $x_{-i}$, the dominating mixture has strictly smaller expected cost than $a$, so $a$ is not a best response and cannot lie in the support of an equilibrium strategy.

## Depends on

- [Strict, weak and ε-strict dominance by mixed strategies](strict-weak-and-strict-dominance-by-mixed-strategies.md)
- [Mixed Nash equilibrium](../is-mixed-nash.md)

## Proof depends on

- [Support characterization of mixed best responses](../support-characterization-of-mixed-best-responses.md)

## Sources

- Eva Tardos and Vijay V. Vazirani, "Basic Solution Concepts and Computational Issues", Algorithmic Game Theory, Cambridge University Press, 2007.
- Noam Nisan, Tim Roughgarden, Eva Tardos and Vijay V. Vazirani, "Algorithmic Game Theory", Cambridge University Press, 2007.
