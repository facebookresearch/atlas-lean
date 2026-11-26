# Eisenberg–Gale convex program for linear Fisher markets

Consider a linear Fisher market with budgets $m_i > 0$, supplies $q_g > 0$, and utilities $u_i(x) = \sum_g a_{ig} x_{ig}$, nondegenerate in the sense that every buyer desires some good and every good is desired by some buyer. The following are equivalent for an allocation $x$ and prices $p$: (a) $(x, p)$ is an equilibrium; (b) the maximum bang-per-buck and KKT conditions hold: every buyer spends its whole budget only on goods maximizing $a_{ig}/p_g$ and every good with positive price is sold; (c) $x$ maximizes the Eisenberg–Gale objective $\sum_i m_i \log u_i(x)$ subject to $\sum_i x_{ig} \le q_g$, $x \ge 0$, with $p$ the optimal dual prices. Consequently an equilibrium exists, the set of equilibrium allocations is convex, and equilibrium utilities and prices are unique.

## Proof sketch

The KKT conditions of the strictly concave (in utilities) program are exactly the equilibrium conditions, with Lagrange multipliers as prices. Strict concavity of the logarithm forces unique utilities, and the dual uniquely determines prices.

## Depends on

- [Fisher market](../exchange-economies/fisher-market.md)
- [Karush–Kuhn–Tucker conditions for inequality constraints](../../../Analysis/convex-analysis-and-variations/karush-kuhn-tucker-inequality.md)

## Proof depends on

- [First welfare theorem for exchange and Fisher markets](../exchange-economies/first-welfare-theorem-for-exchange-and-fisher-markets.md)

## Sources

- Edmund Eisenberg and David Gale, "Consensus of Subjective Probabilities: The Pari-Mutuel Method", The Annals of Mathematical Statistics, 1959.
- Vijay V. Vazirani, "Combinatorial Algorithms for Market Equilibria", Algorithmic Game Theory, Cambridge University Press, 2007.
- Bruno Codenotti and Kasturi Varadarajan, "Computation of Market Equilibria by Convex Programming", Algorithmic Game Theory, Cambridge University Press, 2007.
