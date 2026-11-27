# Cobb–Douglas and CES demands

For Cobb–Douglas utility $u(x) = \prod_g x_g^{a_g}$ with $a_g \ge 0$, $\sum_g a_g = 1$, the Marshallian demand at prices $p > 0$ and income $w$ is $x_g = a_g w / p_g$; Cobb–Douglas exchange economies satisfy WGS, and their equilibrium prices are characterized by a system of linear inequalities. For CES utility $u(x) = (\sum_g a_g x_g^{\rho})^{1/\rho}$ with all $a_g > 0$, $\rho < 1$, $\rho \ne 0$, demand is $x_g = w\, a_g^{\sigma} p_g^{-\sigma} / \sum_h a_h^{\sigma} p_h^{1-\sigma}$ with $\sigma = 1/(1-\rho)$, and CES exchange economies with $0 < \rho < 1$ satisfy WGS (Codenotti, Pemmaraju and Varadarajan), and GS when moreover every trader's endowment is nonzero.

## Proof sketch

Solve the budget-constrained maximization by Lagrange multipliers. For Cobb–Douglas, a trader's spending on good $g$ is a fixed share of its income, which increases when other prices rise; for CES with $\sigma > 1$, $\partial x_g/\partial p_j = a_g^{\sigma} p_g^{-\sigma}\bigl(w_j S + (\sigma - 1)\, W a_j^{\sigma} p_j^{-\sigma}\bigr)/S^2$ for $j \ne g$, where $W = p \cdot w$ is the income from endowment $w$ and $S = \sum_h a_h^{\sigma} p_h^{1-\sigma}$, which is positive when $W > 0$ and $a_g, a_j > 0$.

## Depends on

- [Gross substitutability of an excess-demand function](gross-substitutability-of-an-excess-demand-function.md)
- [Arrow–Debreu exchange market and competitive equilibrium](../exchange-economies/arrow-debreu-exchange-market-and-competitive-equilibrium.md)

## Sources

- Bruno Codenotti and Kasturi Varadarajan, "Computation of Market Equilibria by Convex Programming", Algorithmic Game Theory, Cambridge University Press, 2007.
- Bruno Codenotti, Sriram Pemmaraju and Kasturi Varadarajan, "On the Polynomial Time Computation of Equilibria for Certain Exchange Economies", Proceedings of the Sixteenth Annual ACM-SIAM Symposium on Discrete Algorithms (SODA 2005), 2005.
