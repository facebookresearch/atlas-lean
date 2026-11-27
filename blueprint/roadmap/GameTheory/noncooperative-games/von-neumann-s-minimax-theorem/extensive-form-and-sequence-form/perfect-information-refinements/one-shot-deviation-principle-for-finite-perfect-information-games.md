# One-shot deviation principle for finite perfect-information games

A pure profile of a finite perfect-information game without chance nodes is a subgame-perfect equilibrium if and only if at every decision node $u$ of every player $i$, the choice prescribed at $u$ maximizes player $i$'s payoff among all choices at $u$, assuming the profile is followed in every subtree below $u$.

## Proof sketch

Necessity is immediate. For sufficiency argue by induction on the height of subtrees: any profitable deviation in a subtree can be shortened to its topmost deviating node, because below it the profile is already optimal.

## Depends on

- [Subgame-perfect equilibrium of a perfect-information game](subgame-perfect-equilibrium-of-a-perfect-information-game.md)

## Sources

- Martin J. Osborne and Ariel Rubinstein, *A Course in Game Theory*, MIT Press, 1994, Lemma 98.2 (the one deviation property: in a finite horizon extensive game with perfect information, a strategy profile is a subgame perfect equilibrium if and only if no player can gain in any subgame by a strategy that differs from the profile only in the action it prescribes after the initial history of that subgame).
- Martin J. Osborne, *An Introduction to Game Theory*, Oxford University Press, 2004, Chapter 5 (freely available from the author's site with the publisher's permission), Section 5.5, Proposition 172.1 (the subgame perfect equilibria of a finite horizon extensive game with perfect information are exactly the strategy profiles isolated by backward induction, that is, the profiles in which the action of the player who moves at the start of each subgame is optimal given the profile in all shorter subgames).
- Bernhard von Stengel, "Equilibrium Computation for Two-Player Games in Strategic and Extensive Form", Algorithmic Game Theory, Cambridge University Press, 2007.
