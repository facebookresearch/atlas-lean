# PLS-completeness persists for network congestion games with linear delays

Computing a pure Nash equilibrium is PLS-complete already for asymmetric network congestion games in which every edge has a linear delay function $d_e(x) = a_e x$ with $a_e \ge 0$, and better-response dynamics can need exponentially many steps in such games. The hardness also holds for congestion games whose strategy spaces are bases of matroids intersected with one further combinatorial constraint, so the matroid condition cannot be relaxed.

## Proof sketch

Start from the tight reduction from Local Max-Cut to congestion games with arbitrary nondecreasing delays and replace each resource with a nonlinear delay by a network gadget of parallel and serial edges with linear delays whose induced delay as a function of the number of users matches the required values on the relevant load range. Tightness is preserved, so exponential improvement sequences carry over.

## Depends on

- [Congestion game](../../potential-games/congestion-game.md)
- [PLS reduction and tight PLS reduction](pls-reduction-and-tight-reduction.md)

## Proof depends on

- [Pure Nash equilibria of congestion games are PLS-complete to compute](congestion-game-pure-nash-pls-complete.md)

## Sources

- H. Ackermann, H. Röglin, B. Vöcking, "On the Impact of Combinatorial Structure on Congestion Games", Journal of the ACM 55(6) (2008); FOCS 2006.
