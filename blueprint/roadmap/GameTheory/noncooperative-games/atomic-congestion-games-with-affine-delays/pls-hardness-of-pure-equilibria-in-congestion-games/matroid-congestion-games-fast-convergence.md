# Matroid congestion games converge in polynomially many best responses

In a congestion game in which each player's strategy set is the set of bases of a matroid on the resources (matroid congestion game), every sequence of best responses reaches a pure Nash equilibrium after at most $n^2 m\, \mathrm{rk}$ steps, where $n$ is the number of players, $m$ the number of resources and $\mathrm{rk}$ the maximum rank. Conversely, the matroid property is the maximal such condition: for every non-matroid set system there is a congestion game with that strategy structure in which best-response sequences can be exponentially long.

## Proof sketch

In a matroid, a best response can be reached from the current basis by a sequence of single exchanges, each improving the player's cost; consider a potential counting the delay values in rank order. Each single exchange strictly lowers this rank-based potential, which takes only polynomially many values. For the converse, any non-matroid set system contains a configuration violating the exchange property, which can be used as a gadget to embed an exponential-length Local Max-Cut improvement path.

## Depends on

- [Congestion game](../../potential-games/congestion-game.md)
- [Improving move](../../potential-games/improving-move.md)
- [Pure Nash equilibrium](../../potential-games/is-pure-nash.md)

## Proof depends on

- [Finite improvement property](../../potential-games/well-founded-improving-move.md)
- [Pure Nash equilibria of congestion games are PLS-complete to compute](congestion-game-pure-nash-pls-complete.md)

## Sources

- H. Ackermann, H. Röglin, B. Vöcking, "On the Impact of Combinatorial Structure on Congestion Games", Journal of the ACM 55(6) (2008); FOCS 2006.
