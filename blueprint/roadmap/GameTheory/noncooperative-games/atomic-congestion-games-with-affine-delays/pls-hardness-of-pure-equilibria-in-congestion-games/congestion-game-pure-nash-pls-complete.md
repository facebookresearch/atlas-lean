# Pure Nash equilibria of congestion games are PLS-complete to compute

Computing a pure Nash equilibrium of a congestion game, given explicitly by resources with nondecreasing delay functions and the players' strategy sets as lists of resource subsets, is PLS-complete. The same holds for symmetric congestion games, where all players have the same strategy set, and for network congestion games where strategies are directed paths between player-specific source-sink pairs. The reductions preserve the relevant properties of the source problem, so in all three cases there are games and initial profiles from which every equilibrium is exponentially far in the better-response graph, and finding an equilibrium reachable from a given profile is PSPACE-complete.

## Proof sketch

Membership in PLS uses Rosenthal's potential as the local search objective. For hardness of general games, reduce from positive not-all-equal 3-SAT with the flip neighbourhood: the variables are the players, each with two strategies (true, false); each clause $c$ of weight $w$ gives two resources $e_c, e'_c$ with delay $0$ for at most two users and $w$ otherwise, and a variable's true (false) strategy uses $e_c$ ($e'_c$) for every clause containing it, so pure equilibria are exactly the local optima. Symmetric games are obtained by adding to player $i$'s strategies a private resource $e_i$ whose delay is $0$ for one user and huge for two or more, which forces the players into distinct roles. Network games use a more involved reduction from an extended satisfiability problem, embedding the strategy sets as path systems. (Ackermann, Röglin and Vöcking give an alternative reduction from Local Max-Cut.)

## Depends on

- [Congestion game](../../potential-games/congestion-game.md)
- [PLS reduction and tight PLS reduction](pls-reduction-and-tight-reduction.md)
- [Pure Nash equilibrium](../../potential-games/is-pure-nash.md)
- [The class PLS of polynomial local search problems](../../../../TheoryOfComputation/complexity-classes/total-search-problems/the-class-pls-of-polynomial-local-search.md)

## Proof depends on

- [Pure Nash equilibria of explicit congestion games are in PLS](../atomic-congestion-efficiency/pure-nash-equilibria-of-explicit-congestion-games-are-in-pls.md)
- [Local Max-Cut under the flip neighbourhood is PLS-complete](local-max-cut-flip-pls-complete.md)
- [Rosenthal's theorem](../../potential-games/is-exact-potential-potential.md)
- [Pure equilibria of potential games as local search](../../potential-games/pure-equilibria-of-potential-games-as-local-search.md)
- [Rosenthal's potential](../../potential-games/potential.md)

## Sources

- A. Fabrikant, C. Papadimitriou, K. Talwar, "The Complexity of Pure Nash Equilibria", STOC 2004, Theorem 3 and Corollary 1.
- H. Ackermann, H. Röglin, B. Vöcking, "On the Impact of Combinatorial Structure on Congestion Games", Journal of the ACM 55(6) (2008); FOCS 2006.
