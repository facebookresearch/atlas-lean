# Uniqueness of the subgame-perfect equilibrium without continuation ties

In a finite extensive game with perfect information (without chance nodes), backward induction produces a pure subgame-perfect equilibrium, which is in particular a pure Nash equilibrium (Osborne, Proposition 173.1; von Stengel, Section 3.8). Moreover, in any such game in which the backward-induction procedure selects a single optimal action for the player who moves at the start of each subgame (no continuation ties), the strategy profile selected by backward induction is the unique pure subgame-perfect equilibrium (Osborne, Section 5.5, p. 170 and Proposition 172.1).

## Proof sketch

By Proposition 172.1 (equivalently, the one-shot deviation principle), the set of subgame-perfect equilibria of a finite-horizon perfect-information game is exactly the set of strategy profiles isolated by backward induction. When backward induction selects a single optimal action at every decision node, that set is a singleton. In particular, if no player has the same payoff at any two leaves, then distinct actions at a decision node lead to disjoint subtrees and hence to distinct leaves, so the moving player's optimal choice is unique at every step of backward induction (compare Mas-Colell, Whinston and Green, Propositions 9.B.1 and 9.B.2).

## Depends on

- [Subgame-perfect equilibrium of a perfect-information game](subgame-perfect-equilibrium-of-a-perfect-information-game.md)

## Proof depends on

- [One-shot deviation principle for finite perfect-information games](one-shot-deviation-principle-for-finite-perfect-information-games.md)
- [Exists is Backward Induction is Subgame Perfect](../../../backward-induction-and-subgame-perfection/exists-is-backward-induction-is-subgame.md)

## Sources

- Andreu Mas-Colell, Michael D. Whinston and Jerry R. Green, *Microeconomic Theory*, Oxford University Press, 1995, Proposition 9.B.1 and its proof (if no player has the same payoffs at any two terminal nodes, the optimal actions are unique at every stage of backward induction) and Proposition 9.B.2 (every finite game of perfect information has a pure strategy subgame perfect Nash equilibrium, which is unique if no player has the same payoffs at any two terminal nodes).
- Martin J. Osborne, *An Introduction to Game Theory*, Oxford University Press, 2004, Chapter 5 (freely available from the author's site with the publisher's permission), Section 5.5, Proposition 172.1 (the subgame perfect equilibria of a finite horizon extensive game with perfect information are exactly the strategy profiles isolated by backward induction), the remark before it that when the procedure selects a single action for the player who moves at the start of each subgame, the profile it selects is the unique subgame perfect equilibrium, and Proposition 173.1 (every finite extensive game with perfect information has a subgame perfect equilibrium).
- Bernhard von Stengel, "Equilibrium Computation for Two-Player Games in Strategic and Extensive Form", Algorithmic Game Theory, Cambridge University Press, 2007.
