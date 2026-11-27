# Approximate pure equilibria: fast for bounded jumps, PLS-hard in general

In a symmetric congestion game whose delay functions satisfy the bounded-jump condition $d_e(x + 1) \le \beta\, d_e(x)$, $\varepsilon$-Nash dynamics (only moves improving a player's cost by a factor at least $1 + \varepsilon$, choosing the largest improvement) reach an $\varepsilon$-approximate pure Nash equilibrium from any initial state within $\lceil n \beta \varepsilon^{-1} \log(n C) \rceil$ steps, where $C$ bounds the cost of any player; this is polynomial in $n$, $1/\varepsilon$, $\beta$ and the input size. Without symmetry, computing an $\alpha$-approximate pure Nash equilibrium of a congestion game, a state in which no player can lower her cost by a factor of at least $\alpha$, is PLS-complete for every polynomial-time computable $\alpha > 1$; moreover, finding such an equilibrium reachable from a given state by $\alpha$-improving steps is PSPACE-complete.

## Proof sketch

For symmetric games, every $\varepsilon$-move by the player with largest relative gain reduces Rosenthal's potential by a factor $1 - \Omega(\varepsilon/(\beta n))$, because under bounded jumps any player can imitate any other player's move at a cost overhead of at most a factor $\beta$, so the best mover's gain is a fraction of the potential; logarithmic dependence on the potential range follows. The hardness result is a gap-introducing tight PLS-reduction from Flip (local optima of a function computed by a Boolean circuit), with delays chosen so that every improving move improves by a large factor, making approximate and exact equilibria coincide.

## Depends on

- [Congestion game](../../potential-games/congestion-game.md)
- [PLS reduction and tight PLS reduction](pls-reduction-and-tight-reduction.md)
- [Pure Nash equilibrium](../../potential-games/is-pure-nash.md)
- [The class PLS of polynomial local search problems](../../../../TheoryOfComputation/complexity-classes/total-search-problems/the-class-pls-of-polynomial-local-search.md)

## Proof depends on

- [Pure Nash equilibria of congestion games are PLS-complete to compute](congestion-game-pure-nash-pls-complete.md)
- [Rosenthal's theorem](../../potential-games/is-exact-potential-potential.md)
- [Rosenthal's potential](../../potential-games/potential.md)

## Sources

- S. Chien, A. Sinclair, "Convergence to Approximate Nash Equilibria in Congestion Games", SODA 2007; Games and Economic Behavior 71(2) (2011), Theorem 1.1.
- A. Skopalik, B. Vöcking, "Inapproximability of Pure Nash Equilibria", STOC 2008.
