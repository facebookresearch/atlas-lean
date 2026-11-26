# Von Neumann's minimax theorem over every linearly ordered field

Let $K$ be a linearly ordered field and $M$ an $I \times J$ matrix over $K$ with $I, J$ finite and nonempty, the row player paying $M_{ij}$ to the column player. Call $v \in K$ a *value* of the game if there is a mixed strategy $p \in K^I$ ($p \ge 0$, $\sum_i p_i = 1$) with $\sum_i p_i M_{ij} \le v$ for every column $j$ and a mixed strategy $q \in K^J$ with $\sum_j q_j M_{ij} \ge v$ for every row $i$. Then the game has a value, it is unique, and optimal strategies exist with entries in $K$; in particular a game with rational payoffs has a rational value and rational optimal strategies. Against any mixed strategy of one player, the other has a pure strategy doing at least as well as the value.

## Proof sketch

Shift $M$ by a constant so all entries are positive; then the row player's problem, normalized by its value, is the linear program $\max\{\sum_i x_i : x \ge 0,\ \sum_i x_i M_{ij} \le 1\ \forall j\}$ and the column player's problem is its dual. Linear-programming duality over $K$ (provable by Fourier-Motzkin elimination, with no topology) gives equal optima, and rescaling yields optimal strategies with entries in $K$. Uniqueness follows by playing the two optimal strategies against each other.

## Depends on

- [Von Neumann's minimax theorem](../../../GameTheory/noncooperative-games/von-neumann-s-minimax-theorem/matrix-game-minimax.md)

## Proof depends on

- [Strong linear programming duality](../../../Geometry/convex-geometry/linear-programming/strong-linear-programming-duality.md)
- [Exists nonneg mul Vec eq iff](../../../Geometry/convex-geometry/linear-programming/exists-nonneg-mul-vec-eq-iff.md)

## Sources

- John von Neumann, "Zur Theorie der Gesellschaftsspiele", Mathematische Annalen 100, 1928.
- Jiří Matoušek and Bernd Gärtner, "Understanding and Using Linear Programming", Springer, 2007.
