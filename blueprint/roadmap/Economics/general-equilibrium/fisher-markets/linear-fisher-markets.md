# Linear Fisher markets

A linear Fisher market has a finite set of buyers $i$ with budgets $e_i > 0$, a finite set of divisible goods $j$ with unit supply, and
utilities $u_i(x_i) = \sum_j u_{ij} x_{ij}$ with $u_{ij} \ge 0$, every buyer having $u_{ij} > 0$ for some $j$ and every good desired by
some buyer. Prices $p \ge 0$ and an allocation $x \ge 0$ with $\sum_i x_{ij} \le 1$ for every good $j$ form an equilibrium if each buyer's
bundle maximizes her utility among bundles of cost at most $e_i$ at prices $p$, and every good with positive price is fully sold.
Chakrabarty, Devanur and Vazirani define equilibrium instead by three conditions: every positively priced good is fully sold, a buyer
receives only goods maximizing $u_{ij}/p_j$, and every buyer spends exactly $e_i$.

## Expansion

This node states a precise definition. A good expansion adds pages for the following results about it, with their own dependency
sections:

- at an equilibrium every price is positive, since a buyer who desires a free good has no utility-maximizing bundle;
- when all prices are positive, the definition above and the three conditions of the source define the same equilibria.

## Sources

- D. Chakrabarty, N. R. Devanur and V. V. Vazirani, *Rationality and Strongly Polynomial Solvability of Eisenberg–Gale Markets with Two Agents*, §2.1 (the linear Fisher market and the equilibrium conditions (1)–(3)). <https://www-dev.ics.uci.edu/~vazirani/EG2.pdf>
