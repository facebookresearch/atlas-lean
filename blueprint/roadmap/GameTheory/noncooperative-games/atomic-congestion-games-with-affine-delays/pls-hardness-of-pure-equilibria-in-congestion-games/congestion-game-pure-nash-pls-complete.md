# Pure Nash equilibria of congestion games are PLS-complete to compute

Computing a pure Nash equilibrium of a congestion game, given explicitly by resources with nondecreasing delay functions and the players' strategy sets as lists of resource subsets, is PLS-complete. The same holds for symmetric congestion games, where all players have the same strategy set, and for network congestion games where strategies are directed paths between player-specific source-sink pairs. The reductions are tight, so better-response dynamics can require exponentially many steps from some initial profiles.

## Proof sketch

Membership in PLS uses Rosenthal's potential as the local search objective. For hardness, reduce Local Max-Cut: each edge becomes two resources whose delays reward separating its endpoints, and each vertex becomes a player choosing between two strategies corresponding to the sides of the cut; the potential equals a constant minus the cut weight. Symmetric games are handled by adding a gadget that forces players into distinct roles, and network games by embedding strategy sets as path systems.

## Depends on

- [Congestion game](../../potential-games/congestion-game.md)
- [PLS reduction and tight PLS reduction](pls-reduction-and-tight-reduction.md)
- [Pure Nash equilibrium](../../potential-games/is-pure-nash.md)
- [The class PLS of polynomial local search problems](../../../../TheoryOfComputation/complexity-classes/total-search-problems/the-class-pls-of-polynomial-local-search.md)

## Proof depends on

- [Local Max-Cut under the flip neighbourhood is PLS-complete](local-max-cut-flip-pls-complete.md)
- [Rosenthal's theorem](../../potential-games/is-exact-potential-potential.md)
- [Pure equilibria of potential games as local search](../../potential-games/pure-equilibria-of-potential-games-as-local-search.md)
- [Rosenthal's potential](../../potential-games/potential.md)

## Sources

- A. Fabrikant, C. Papadimitriou, K. Talwar, "The Complexity of Pure Nash Equilibria", STOC 2004.
- H. Ackermann, H. Röglin, B. Vöcking, "On the Impact of Combinatorial Structure on Congestion Games", Journal of the ACM 55(6) (2008); FOCS 2006.
