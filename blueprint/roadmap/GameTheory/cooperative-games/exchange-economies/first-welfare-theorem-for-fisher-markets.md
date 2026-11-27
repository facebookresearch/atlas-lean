# First welfare theorem for Fisher markets

In a Fisher market whose buyers have locally nonsatiated utilities, the allocation of every equilibrium is Pareto optimal among feasible allocations: no allocation that oversells no good makes every buyer weakly better off and some buyer strictly better off. No convexity or continuity assumption is needed. The exchange-economy case is the first welfare theorem for Walrasian equilibria.

## Proof sketch

A Pareto improvement $y$ must cost each buyer at least its budget at the equilibrium prices $p$, and strictly more for the strictly better-off buyer, by local nonsatiation. Since every good with positive price is fully sold at equilibrium, the budgets sum to at least $p \cdot q$, so $p \cdot \sum_i y_i > p \cdot q$, contradicting the feasibility of $y$ with $p \ge 0$. Equivalently, apply the first welfare theorem for exchange economies through the proportional-endowment embedding.

## Depends on

- [Fisher market](fisher-market.md)

## Proof depends on

- [Walrasian equilibrium allocations are Pareto efficient](../../../Economics/general-equilibrium/first-welfare-theorem/is-pareto-efficient-of-is-walrasian-equi.md)
- [Fisher markets embed into exchange markets](fisher-markets-embed-into-exchange-markets.md)

## Sources

- Kenneth J. Arrow and Gerard Debreu, "Existence of an Equilibrium for a Competitive Economy", Econometrica, 1954.
- Bruno Codenotti and Kasturi Varadarajan, "Computation of Market Equilibria by Convex Programming", Algorithmic Game Theory, Cambridge University Press, 2007.
