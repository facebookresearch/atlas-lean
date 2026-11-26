# Approximate pure equilibria: fast for bounded jumps, PLS-hard in general

In a symmetric congestion game whose delay functions satisfy the bounded-jump condition $d_e(x + 1) \le \beta\, d_e(x)$, $\varepsilon$-Nash dynamics (only moves improving a player's cost by a factor at least $1 + \varepsilon$, choosing the largest improvement) reach an $\varepsilon$-approximate pure Nash equilibrium within a number of steps polynomial in $n$, $1/\varepsilon$ and $\beta$. Without symmetry, computing an $\varepsilon$-approximate pure Nash equilibrium of a congestion game with increasing delays is PLS-complete for every polynomial-time computable $\varepsilon$.

## Proof sketch

For symmetric games, every $\varepsilon$-move by the player with largest gain reduces Rosenthal's potential by a factor $1 - \Omega(\varepsilon/(\beta n))$, because the gain of the best mover is comparable to the average gain and hence to a fraction of the potential; logarithmic dependence on the potential range follows. The hardness result encodes Local Max-Cut with delays chosen so that the multiplicative gaps between alternative strategies are huge, making approximate and exact equilibria coincide.

## Depends on

- [Congestion game](../../potential-games/congestion-game.md)
- [PLS reduction and tight PLS reduction](pls-reduction-and-tight-reduction.md)
- [Pure Nash equilibrium](../../potential-games/is-pure-nash.md)
- [The class PLS of polynomial local search problems](../../../../TheoryOfComputation/complexity-classes/total-search-problems/the-class-pls-of-polynomial-local-search.md)

## Proof depends on

- [Pure Nash equilibria of congestion games are PLS-complete to compute](congestion-game-pure-nash-pls-complete.md)
- [Rosenthal's theorem](../../potential-games/is-exact-potential-potential.md)
- [Local Max-Cut under the flip neighbourhood is PLS-complete](local-max-cut-flip-pls-complete.md)
- [Rosenthal's potential](../../potential-games/potential.md)

## Sources

- S. Chien, A. Sinclair, "Convergence to Approximate Nash Equilibria in Congestion Games", SODA 2007; Games and Economic Behavior 71(2) (2011).
- A. Skopalik, B. Vöcking, "Inapproximability of Pure Nash Equilibria", STOC 2008.
