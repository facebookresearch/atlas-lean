# Symmetrization reduces bimatrix Nash equilibria to symmetric ones

Let $(A, B)$ be an $m \times n$ bimatrix game with all payoffs positive and form the symmetric $(m + n) \times (m + n)$ game with matrix $\begin{pmatrix} 0 & A \\ B^\top & 0 \end{pmatrix}$. If $z = (x, y)$ is a symmetric Nash equilibrium of the symmetrized game, then both $x$ and $y$ are nonzero and $\bigl(x / \sum x,\ y / \sum y\bigr)$ is a Nash equilibrium of $(A, B)$. Conversely every Nash equilibrium of $(A, B)$ arises this way from a symmetric equilibrium. Adding a constant to all payoffs reduces arbitrary games to the positive case.

## Proof sketch

If $x = 0$ then the payoff to every row strategy of the first block would be positive, contradicting that $z$'s support consists of best responses; similarly for $y$. The best-response conditions of the symmetrized game split into those of the two original players.

## Depends on

- [Player-symmetric game and symmetric equilibrium](player-symmetric-game-and-symmetric-equilibrium.md)
- [Nash equilibrium of a bimatrix game](../../bimatrix-games-and-the-lemke-howson-algorithm/is-bimatrix-nash.md)

## Sources

- Christos H. Papadimitriou, "The Complexity of Finding Nash Equilibria", Algorithmic Game Theory, Cambridge University Press, 2007.
- Bernhard von Stengel, "Equilibrium Computation for Two-Player Games in Strategic and Extensive Form", Algorithmic Game Theory, Cambridge University Press, 2007.
