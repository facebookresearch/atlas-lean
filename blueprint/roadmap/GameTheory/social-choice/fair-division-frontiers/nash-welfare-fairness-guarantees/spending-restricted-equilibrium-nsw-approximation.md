# Spending-restricted equilibria give a constant-factor Nash welfare approximation

Throughout, $N = \{1, \dots, n\}$ is a finite set of agents and $M$ a finite set of indivisible goods; agent $i$ has an additive valuation $v_i(S) = \sum_{g \in S} v_i(g)$ with $v_i(g) \ge 0$. A spending-restricted outcome of the fractional Fisher market with unit budgets is a price vector $p \ge 0$ and a fractional allocation in which each agent spends her whole budget on goods of maximum bang-per-buck $v_i(g)/p_g$ and the total spending on each good $g$ equals $\min\{1, p_g\}$. Rounding such an outcome yields a polynomial-time algorithm that is a $2 e^{1/e} \approx 2.889$-approximation for maximum Nash social welfare with additive valuations.

## Proof sketch

Scale each agent's values so that $v_i(g) = p_g$ on her maximum bang-per-buck goods. The spending-restricted prices give an upper bound on the geometric mean of the optimal integral allocation in terms of the prices, in which the goods of price above $1$ (where spending is capped) enter separately. The rounding assigns each good of price above $1$ to a distinct agent for whom it is a maximum bang-per-buck good, and rounds the rest of the spending forest, giving leaves and goods of price at most $\tfrac12$ to their parent agents and matching the remaining goods. Each agent's value is compared with her spending in the outcome, and the worst case of the comparison gives the factor $2e^{1/e}$.

## Depends on

- [Approximation ratio for the Nash social welfare objective](nash-social-welfare-approximation-ratio.md)
- [Maximum bang-per-buck allocation supported by prices](../market-equilibria-for-fair-and-efficient-allocation/maximum-bang-per-buck-allocation.md)

## Sources

- R. Cole, V. Gkatzelis, "Approximating the Nash Social Welfare with Indivisible Items", STOC 2015; SIAM Journal on Computing 47(3) (2018).
