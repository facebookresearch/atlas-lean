# Weak Allee effect from a high-density growth switch

In the [binary switch model](binary-switch-model-of-threshold-dependent-growth.md) take $r = 0$ and $R > 0$: individuals with at most $M$ occupied neighbours neither proliferate nor die. The model reduces to $\frac{1}{RC}\frac{dC}{dt} = \mathcal S(C; \beta, M)$ with

$$\mathcal S(C; \beta, M) = -\beta C^6 + \mathbf 1(M \le 4)\sum_{j=M+1}^{5} \binom5j C^j (1-C)^{6-j}\Bigl[1 - \frac{6\beta}{6-j}\Bigr]. \tag{6}$$

**Equilibria.** The source reports, from the tabulated functions $f_M$ below and numerical checks of their monotonicity, that a nonzero equilibrium $C_1 \in (0, 1]$ exists exactly when $M \le 4$ and $0 \le \beta < (5 - M)/6$; it is then unique and stable, while $C^* = 0$ is unstable, which is a weak Allee effect (growth deviating from logistic without extra equilibria). If $M \le 4$ and $\beta \ge (5 - M)/6$, or $M = 5$ and $\beta > 0$, then $C^* = 0$ is the only equilibrium in $[0, 1]$ and it is stable (extinction). If $M = 5$ and $\beta = 0$, then $\mathcal S \equiv 0$: there is no growth at all and every density in $[0, 1]$ is stationary, so this case is excluded from the count of isolated equilibria. Since (6) is linear in $\beta$, the equilibrium is described by $\beta = f_M(C_1)$; for example

$$f_4(C_1) = \frac{1 - C_1}{6 - 5C_1}, \qquad f_3(C_1) = \frac{4C_1^2 - 9C_1 + 5}{10C_1^2 - 24C_1 + 15}.$$

**The case $M = 4$ explicitly.** Here $\mathcal S(C; \beta, 4) = C^5\bigl[(1 - 6\beta) - (1 - 5\beta)C\bigr]$, so for $0 \le \beta < 1/6$ the nonzero equilibrium is

$$C_1 = \frac{1 - 6\beta}{1 - 5\beta} \in (0, 1],$$

with $\mathcal S > 0$ on $(0, C_1)$ and $\mathcal S < 0$ on $(C_1, 1]$; for $\beta \ge 1/6$, $\mathcal S < 0$ on $(0, 1]$. Near $0$ the per-capita growth rate vanishes like $C^5$ instead of tending to a positive constant, so small populations grow far more slowly than in the logistic model.

## Depends on

- [Binary switch model of threshold-dependent growth](binary-switch-model-of-threshold-dependent-growth.md)

## Proof depends on

Its proof consists of the steps listed under Expansion.

## Expansion

For $M = 4$ only $j = 5$ contributes: $C^5(1 - C)(1 - 6\beta) - \beta C^6$. Solving $(1 - C)(1 - 6\beta) = \beta C$ gives $C_1$, and the sign pattern follows from linearity of the bracket in $C$ (its slope $-(1 - 5\beta)$ is negative for $\beta < 1/5$). Inverting, $1 - C_1 = \beta(6 - 5C_1)$ gives $f_4$. For $M = 5$ only the term $-\beta C^6$ remains, so the sign of $\mathcal S$ on $(0, 1]$ is that of $-\beta$. For general $M \le 4$ the source tabulates $f_M$ and reports, from plots of $f_M$, that it is one-to-one on $(0, 1]$ with range $[0, (5 - M)/6)$; the $M = 4$ case above is a complete proof for that threshold.

## Sources

- N. T. Fadai and M. J. Simpson, *Population dynamics with threshold effects give rise to a diverse family of Allee effects*, Bull. Math. Biol. (2020), <https://doi.org/10.1007/s11538-020-00756-5>, PMCID PMC7292819 (Section 2.1, Case 1; equation (6) and Table 3).
