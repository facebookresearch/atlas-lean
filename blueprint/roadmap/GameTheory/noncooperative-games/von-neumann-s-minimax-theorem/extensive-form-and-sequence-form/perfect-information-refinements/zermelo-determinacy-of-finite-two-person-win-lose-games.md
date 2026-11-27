# Zermelo determinacy of finite two-person win-lose games

Let $G$ be a two-person game of perfect information played on a finite game tree, in which the two players move alternately and each leaf is labelled as a win for one of the two players (no ties). Then one of the two players has a winning strategy, that is, a strategy that guarantees reaching a leaf labelled as a win for that player whatever the other player does.

## Proof sketch

Define by recursion on the finite tree whether the player to move can force a win: a leaf is won by its labelled winner, and a position is winning for the mover iff some move leads to a position winning for the mover. The recursion yields a strategy for whichever player wins at the root.

## Depends on

- [Perfect-information game tree](../../../backward-induction-and-subgame-perfection/perfect-info-game.md)

## Sources

- Anna R. Karlin and Yuval Peres, *Game Theory, Alive*, American Mathematical Society, 2017, Definition 1.0.2 (progressively bounded games) and Theorem 1.2.2 (in any progressively bounded combinatorial game with no ties allowed, one of the players has a winning strategy which depends only upon the current state of the game).
- Bernhard von Stengel, "Equilibrium Computation for Two-Player Games in Strategic and Extensive Form", Algorithmic Game Theory, Cambridge University Press, 2007.
