# Lambert-W solution of the SEIR final-size relation

Let $(s, e, i, r)$ be a solution of the normalized SEIR system

$$\dot s = -\beta s i, \quad \dot e = \beta s i - \alpha e, \quad \dot i = \alpha e - \gamma i, \quad \dot r = \gamma i,$$

with $\alpha, \beta, \gamma > 0$, nonnegative initial data summing to $1$, and basic reproduction number $R_0 = \beta / \gamma$. Write $s_0 = s(0) > 0$, $r_0 = r(0)$, assume an infection is present, $e(0) + i(0) > 0$, and suppose $s(t) \to s_\infty$, $e(t), i(t) \to 0$ and hence $r(t) \to r_\infty = 1 - s_\infty$.

**Final-size relation.** Dividing $\dot s$ by $\dot r$ and integrating gives $\log(s(t)/s_0) = -R_0\,(r(t) - r_0)$ for all $t$, hence

$$s_\infty = s_0 \exp\!\big(-R_0\,(1 - s_\infty - r_0)\big).$$

**Explicit solution.** Let $W_0$ denote the principal branch of the Lambert $W$ function (the inverse of $w \mapsto w e^{w}$ on $[-1, \infty)$). Then

$$s_\infty = -\frac{1}{R_0}\, W_0\!\big(-s_0 R_0\, e^{-R_0 (1 - r_0)}\big), \qquad r_\infty = 1 + \frac{1}{R_0}\, W_0\!\big(-s_0 R_0\, e^{-R_0 (1 - r_0)}\big),$$

and $s_\infty > 0$ whenever $s_0 > 0$: an SEIR epidemic never exhausts the susceptible pool.

## Depends on

- [Final-size relation when S and R have limits](../../seir-epidemic-model/final-size.md)
- [Limits and final size for nonnegative data with σ, γ > 0](../../seir-epidemic-model/tendsto-final-size.md)

## Expansion

Multiply the final-size relation by $-R_0 e^{-R_0 s_\infty}$ to get $(-R_0 s_\infty)\, e^{-R_0 s_\infty} = -s_0 R_0\, e^{-R_0 (1 - r_0)}$, so $-R_0 s_\infty$ is a value of $W$ at the right-hand side $x$. Since $s_0 \le 1 - r_0$, one has $-x \le R_0 (1 - r_0) e^{-R_0(1-r_0)} \le e^{-1}$, so $x \in [-e^{-1}, 0)$ and both real branches are defined. The relevant root is the one with $R_0 s_\infty \le 1$: $s(t)$ decreases, and once $R_0 s(t) < 1$ the infected classes decay, so the limiting susceptible fraction lies below the herd-immunity value $1/R_0$ (the classical threshold property of the final size when $e(0) + i(0) > 0$), and $R_0 s_\infty \le 1$ means $W = -R_0 s_\infty \ge -1$, which selects $W_0$. Without initial infection the trivial solution $s_\infty = s_0$ can lie on the other branch $W_{-1}$, which is why that case is excluded. Positivity follows because $W_0(x) < 0$ for $x < 0$. The latent class does not change the final size, exactly as in the SIR model, because every exposed individual eventually passes through $I$ to $R$.

## Sources

- K. Linka, M. Peirlinck, E. Kuhl, "The reproduction number of COVID-19 and its correlation with public health interventions", Computational Mechanics (2020), Appendix, Eqs. (5)–(17) ("Endemic equilibrium"), <https://doi.org/10.1007/s00466-020-01880-8> (PMC7385940).
