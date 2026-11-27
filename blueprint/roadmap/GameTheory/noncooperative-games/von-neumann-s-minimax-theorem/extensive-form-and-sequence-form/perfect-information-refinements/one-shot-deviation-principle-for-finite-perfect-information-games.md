# One-shot deviation principle for finite perfect-information games

A pure profile of a finite perfect-information game is a subgame-perfect equilibrium if and only if at every decision node $u$ of every player $i$, the choice prescribed at $u$ maximizes player $i$'s expected payoff among all choices at $u$, assuming the profile is followed in every subtree below $u$.

## Proof sketch

Necessity is immediate. For sufficiency argue by induction on the height of subtrees: any profitable deviation in a subtree can be shortened to its topmost deviating node, because below it the profile is already optimal.

## Depends on

- [Subgame-perfect equilibrium of a perfect-information game](subgame-perfect-equilibrium-of-a-perfect-information-game.md)

## Sources

- Bernhard von Stengel, "Equilibrium Computation for Two-Player Games in Strategic and Extensive Form", Algorithmic Game Theory, Cambridge University Press, 2007.
