# Spending-restricted equilibria give a constant-factor Nash welfare approximation

Throughout, $N = \{1, \dots, n\}$ is a finite set of agents and $M$ a finite set of indivisible goods; agent $i$ has an additive valuation $v_i(S) = \sum_{g \in S} v_i(g)$ with $v_i(g) \ge 0$. A spending-restricted equilibrium of the fractional Fisher market with unit budgets is a price vector $p \ge 0$ and a fractional allocation in which each agent spends her whole budget on goods of maximum bang-per-buck $v_i(g)/p_g$ and the money spent on each good is at most $1$. Rounding such an equilibrium yields a polynomial-time algorithm that is a $2 e^{1/e} \approx 2.89$-approximation for maximum Nash social welfare with additive valuations.

## Proof sketch

Spending restriction caps each good's price at one, so a good is never worth more than one unit of budget; the equilibrium's fractional Nash welfare upper-bounds the integral optimum. Integrally assigning goods with price at least one and rounding the remaining low-price forest of fractional assignments loses at most a factor $2$, and an averaging argument over the spending pattern contributes the factor $e^{1/e}$.

## Depends on

- [Approximation ratio for the Nash social welfare objective](nash-social-welfare-approximation-ratio.md)

## Sources

- R. Cole, V. Gkatzelis, "Approximating the Nash Social Welfare with Indivisible Items", STOC 2015; SIAM Journal on Computing 47(3) (2018).
