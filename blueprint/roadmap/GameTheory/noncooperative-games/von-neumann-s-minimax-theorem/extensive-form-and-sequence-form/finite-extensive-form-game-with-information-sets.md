# Finite extensive-form game with information sets

A *finite extensive-form game* consists of a finite rooted tree whose leaves carry payoff vectors, whose chance nodes carry probability distributions over their children, and whose decision nodes are each assigned to a player $i$ and to an information set $h \in H_i$; all nodes in $h$ have the same set $C_h$ of choices. A *pure strategy* of player $i$ selects one choice at every information set of $i$; a *mixed strategy* is a distribution over pure strategies; a *behavior strategy* assigns a probability distribution over $C_h$ independently at every $h \in H_i$. Each profile induces a distribution on leaves and expected payoffs.

## Depends on

- [Strategic Game](../../../not-yet-classified/part-02/strategic-game/strategic-game.md)
- [Perfect-information game tree](../../backward-induction-and-subgame-perfection/perfect-info-game.md)

## Sources

- Bernhard von Stengel, "Equilibrium Computation for Two-Player Games in Strategic and Extensive Form", Algorithmic Game Theory, Cambridge University Press, 2007.
