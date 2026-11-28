# A Walrasian equilibrium exists iff the LP relaxation has an integral optimum

For finitely many bidders and items with real valuations satisfying $v_i(\emptyset) \ge 0$, a Walrasian equilibrium exists if and only if the LP relaxation admits an optimal solution with all coordinates in $\{0, 1\}$. Valuations with complementarities can rule out Walrasian equilibria: with two items $a, b$, a bidder valuing only the bundle $\{a, b\}$, at $3$, and a unit-demand bidder valuing every nonempty bundle at $2$, no Walrasian equilibrium exists.

## Proof sketch

Combine both welfare theorems. For the counterexample, an equilibrium allocation maximizes welfare, so the pair goes to the first bidder; keeping the unit-demand bidder from demanding an item needs both prices at least $2$, while the first bidder demands the pair only if the prices sum to at most $3$.

## Depends on

- [Combinatorial auction LP relaxation and Walrasian equilibrium](combinatorial-auction-lp-relaxation-and-walrasian-equilibrium.md)

## Proof depends on

- [First welfare theorem for combinatorial auctions](first-welfare-theorem-for-combinatorial-auctions.md)
- [Second welfare theorem for combinatorial auctions](second-welfare-theorem-for-combinatorial-auctions.md)

## Sources

- Liad Blumrosen and Noam Nisan, "Combinatorial Auctions", Algorithmic Game Theory, Cambridge University Press, 2007.
