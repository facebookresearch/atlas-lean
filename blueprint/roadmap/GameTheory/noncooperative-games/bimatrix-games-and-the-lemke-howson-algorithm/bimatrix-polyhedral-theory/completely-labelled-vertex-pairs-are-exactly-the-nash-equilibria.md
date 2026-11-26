# Completely labelled vertex pairs are exactly the Nash equilibria

Let $(A, B)$ be a bimatrix game with all payoffs positive. If $(x, y) \in P \times Q$ is completely labelled and $(x, y) \ne (0, 0)$, then $\bigl(x / \sum_i x_i,\ y / \sum_j y_j\bigr)$ is a Nash equilibrium; conversely every Nash equilibrium $(\bar x, \bar y)$ arises this way from the completely labelled pair $(\bar x / v, \bar y / u)$, where $u = \bar x^\top A \bar y$ and $v = \bar x^\top B \bar y$ are the equilibrium payoffs of the row and column player. If the game is nondegenerate, completely labelled pairs are pairs of vertices of $P$ and $Q$.

## Proof sketch

Complementary labels say that each pure strategy is either unused or a best response, which is the support characterization of equilibria after rescaling by the payoffs.

## Depends on

- [Best response polytopes of a bimatrix game](best-response-polytopes-of-a-bimatrix-game.md)
- [Nondegenerate bimatrix game](../is-nondegenerate.md)

## Proof depends on

- [Support characterization of mixed best responses](../../nash-s-theorem/support-characterization-of-mixed-best-responses.md)

## Sources

- Bernhard von Stengel, "Equilibrium Computation for Two-Player Games in Strategic and Extensive Form", Algorithmic Game Theory, Cambridge University Press, 2007.
