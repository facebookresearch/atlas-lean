# Approximate pure equilibria: fast for bounded jumps, PLS-hard in general

Consider a symmetric congestion game with $n$ players whose delay functions $d_e : \{1, \dots, n\} \to \mathbb{N}$ are nondecreasing with nonnegative integer values and satisfy the bounded-jump condition $d_e(x + 1) \le \beta\, d_e(x)$ for $x \ge 1$. For $\varepsilon \in (0, 1)$, call a move an $\varepsilon$-move if it lowers the moving player's cost from $c$ to some $c' < (1 - \varepsilon) c$, and a state an $\varepsilon$-Nash equilibrium if no $\varepsilon$-move exists. The $\varepsilon$-Nash dynamics, in which at each step a player with the largest relative improvement $(c - c')/c$ makes an $\varepsilon$-move, reaches an $\varepsilon$-Nash equilibrium from any initial state within $\lceil n \beta \varepsilon^{-1} \log(n C) \rceil$ steps, where $C$ bounds the cost of any player; this is polynomial in $n$, $1/\varepsilon$, $\beta$ and the input size. For the ratio form, in which a move must lower the cost by a factor of more than $1 + \varepsilon'$, i.e. $c' < c/(1 + \varepsilon')$, substitute $\varepsilon = \varepsilon'/(1 + \varepsilon')$, which gives $\lceil n \beta (1 + \varepsilon') \varepsilon'^{-1} \log(n C) \rceil$ steps. Without symmetry, computing an $\alpha$-approximate pure Nash equilibrium of a congestion game, a state in which no player can lower her cost by a factor of at least $\alpha$, is PLS-complete for every polynomial-time computable $\alpha > 1$; moreover, finding such an equilibrium reachable from a given state by $\alpha$-improving steps is PSPACE-complete.

## Proof sketch

For symmetric games, every $\varepsilon$-move by the player with largest relative gain reduces Rosenthal's potential by a factor of more than $1 - \varepsilon/(\beta n)$, because under bounded jumps any player can imitate any other player's move at a cost overhead of at most a factor $\beta$, so the best mover's gain is a fraction of the potential; since the potential is a positive integer at most $nC$ unless it is $0$, logarithmic dependence on $nC$ follows. The hardness result is a gap-introducing tight PLS-reduction from Flip (local optima of a function computed by a Boolean circuit), with delays chosen so that every improving move improves by a large factor, making approximate and exact equilibria coincide.

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
