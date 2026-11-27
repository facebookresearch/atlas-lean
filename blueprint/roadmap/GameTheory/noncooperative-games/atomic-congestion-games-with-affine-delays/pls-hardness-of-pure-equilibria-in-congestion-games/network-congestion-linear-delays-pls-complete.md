# PLS-completeness persists for network congestion games with linear delays

Computing a pure Nash equilibrium is PLS-complete already for asymmetric network congestion games, with directed or with undirected edges, in which every edge has a linear delay function $d_e(x) = a_e x$ with $a_e \ge 0$. The reductions are tight, so such games have initial states from which every best-response sequence is exponentially long; by adding a common source and a common sink, the same holds for symmetric network congestion games with linear delays, even though a pure equilibrium of a symmetric network game can be computed in polynomial time.

## Proof sketch

Local Max-Cut, viewed as a party-affiliation game, reduces to a quadratic threshold game: each player either uses a private threshold resource or the set of resources shared with every other player, one resource per pair with delay linear in its load. Embed this game in a grid network: player $i$ goes from the $i$-th node of the first column to the $i$-th node of the last row, either along its own threshold edge or along the row-column path through row $i$ and column $i$; large constant delays on grid edges (made linear, since each is used by one player) make all other paths dominated, and the node where row $j$ meets column $i$ plays the shared resource of players $i$ and $j$, replaced by an edge gadget. Tightness is preserved, so exponential improvement sequences carry over.

## Depends on

- [Congestion game](../../potential-games/congestion-game.md)
- [PLS reduction and tight PLS reduction](pls-reduction-and-tight-reduction.md)
- [Pure Nash equilibrium](../../potential-games/is-pure-nash.md)
- [The class PLS of polynomial local search problems](../../../../TheoryOfComputation/complexity-classes/total-search-problems/the-class-pls-of-polynomial-local-search.md)

## Proof depends on

- [Pure Nash equilibria of congestion games are PLS-complete to compute](congestion-game-pure-nash-pls-complete.md)
- [Local Max-Cut under the flip neighbourhood is PLS-complete](local-max-cut-flip-pls-complete.md)

## Sources

- H. Ackermann, H. Röglin, B. Vöcking, "On the Impact of Combinatorial Structure on Congestion Games", Journal of the ACM 55(6) (2008); FOCS 2006, Theorems 4.1, 4.3, 4.4 and 4.5.
