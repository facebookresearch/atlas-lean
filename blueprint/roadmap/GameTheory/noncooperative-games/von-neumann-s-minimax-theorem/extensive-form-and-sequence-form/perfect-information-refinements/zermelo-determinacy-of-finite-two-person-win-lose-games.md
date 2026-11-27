# Zermelo determinacy of finite two-person win-lose games

Let $G$ be a two-person game of perfect information whose positions form a tree of finite move sequences in which every play is finite (no infinite branch), with a winner assigned to each finished play and an arbitrary player to move at each position (choice sets may be infinite). Then exactly one of the two players has a winning strategy from the initial position, and more generally from every position.

## Proof sketch

Define by well-founded recursion on the position tree whether the player to move can force a win: a finished play is won by its victor, and a position is winning for the mover iff some move leads to a winning position for the mover. The recursion yields a strategy for whichever player wins at the root, and the two possibilities exclude each other.

## Depends on

- [Perfect-information game tree](../../../backward-induction-and-subgame-perfection/perfect-info-game.md)

## Sources

- Bernhard von Stengel, "Equilibrium Computation for Two-Player Games in Strategic and Extensive Form", Algorithmic Game Theory, Cambridge University Press, 2007.
