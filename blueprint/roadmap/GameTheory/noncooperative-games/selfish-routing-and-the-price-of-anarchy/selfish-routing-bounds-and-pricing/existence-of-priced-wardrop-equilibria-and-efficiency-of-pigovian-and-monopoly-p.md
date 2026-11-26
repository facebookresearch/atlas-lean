# Existence of priced Wardrop equilibria and efficiency of Pigovian and monopoly prices

For every price vector and every family of continuous nondecreasing latencies on parallel links, a priced Wardrop equilibrium exists (as a minimizer of a Beckmann-type convex potential over the compact feasible set). If latencies are smooth convex and nondecreasing, then marginal-cost (Pigovian) prices $p_i = x_i \ell_i'(x_i)$ at a social optimum support that optimum as a priced Wardrop equilibrium, and the equilibrium induced by the profit-maximizing prices of a single monopolist owning all links maximizes social surplus; the monopolist's profit plus consumer surplus equals the optimal social surplus.

## Proof sketch

Existence follows by minimizing the convex potential $\sum_i \int_0^{x_i} (\ell_i + p_i) - R \sum_i x_i$. Comparing the KKT conditions of surplus maximization with the equilibrium conditions shows that marginal-cost prices align the two; the monopolist's first-order conditions coincide with those of the social planner.

## Depends on

- [Priced Wardrop equilibrium with reservation utility](priced-wardrop-equilibrium-with-reservation-utility.md)

## Proof depends on

- [Wardrop equilibria are the minimizers of the Beckmann potential](../wardrop-equilibria-minimize-the-beckmann-potential.md)
- [Karush–Kuhn–Tucker conditions for inequality constraints](../../../../Analysis/convex-analysis-and-variations/karush-kuhn-tucker-inequality.md)

## Sources

- Asuman Ozdaglar and R. Srikant, "Incentives and Pricing in Communications Networks", Algorithmic Game Theory, Cambridge University Press, 2007.
- Daron Acemoglu and Asuman Ozdaglar, "Competition and Efficiency in Congested Markets", Mathematics of Operations Research, 2007.
