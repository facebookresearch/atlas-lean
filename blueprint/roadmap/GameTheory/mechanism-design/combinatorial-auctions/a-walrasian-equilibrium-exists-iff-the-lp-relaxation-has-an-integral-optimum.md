# A Walrasian equilibrium exists iff the LP relaxation has an integral optimum

For finitely many bidders and items with real valuations satisfying $v_i(\emptyset) \ge 0$, a Walrasian equilibrium exists if and only if the LP relaxation admits an optimal solution with all coordinates in $\{0, 1\}$. Valuations with complementarities can rule out Walrasian equilibria: with two items and suitable complementary valuations, no Walrasian equilibrium exists.

## Proof sketch

Combine both welfare theorems. For the counterexample, one bidder values only the pair while two others each value a single item, with values making the fractional optimum strictly exceed every integral allocation.

## Depends on

- [Combinatorial auction LP relaxation and Walrasian equilibrium](combinatorial-auction-lp-relaxation-and-walrasian-equilibrium.md)

## Proof depends on

- [First welfare theorem for combinatorial auctions](first-welfare-theorem-for-combinatorial-auctions.md)
- [Second welfare theorem for combinatorial auctions](second-welfare-theorem-for-combinatorial-auctions.md)

## Sources

- Liad Blumrosen and Noam Nisan, "Combinatorial Auctions", Algorithmic Game Theory, Cambridge University Press, 2007.
