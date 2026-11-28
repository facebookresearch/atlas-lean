# Fold change of mRNA across cell-cycle stages

**Model.** A cell alternates between stage $S_1$ (from division until the gene is replicated) and stage $S_2$ (from replication until the next division), with exponentially distributed durations of rates $\kappa_1 > 0$ and $\kappa_2 > 0$. In stage $S_i$ each gene copy follows the two-state promoter model: activation rate $\lambda_i > 0$, inactivation rate $\gamma_i > 0$, transcription at rate $\nu_i > 0$ while active, and mRNA degradation at rate $\delta_i > 0$. Stage $S_1$ has one gene copy and stage $S_2$ two independent copies; every stage starts with all copies OFF, and at the end of $S_2$ each mRNA goes to the tracked daughter independently with probability $1/2$.

**Stationary means.** Let $D = \bigl[2(\delta_1 + \kappa_1)(\delta_2 + \kappa_2) - \kappa_1\kappa_2\bigr]\,(\lambda_1 + \gamma_1 + \kappa_1)(\lambda_2 + \gamma_2 + \kappa_2)$. The stationary mean mRNA numbers within the two stages are

$$m_1^* = \frac{2\nu_1\lambda_1(\delta_2 + \kappa_2)(\lambda_2 + \gamma_2 + \kappa_2) + 2\nu_2\lambda_2\kappa_1(\lambda_1 + \gamma_1 + \kappa_1)}{D},$$

$$m_2^* = \frac{2\nu_1\lambda_1\kappa_2(\lambda_2 + \gamma_2 + \kappa_2) + 4\nu_2\lambda_2(\delta_1 + \kappa_1)(\lambda_1 + \gamma_1 + \kappa_1)}{D},$$

and the population mean is $m^* = m_1^*\,\kappa_2/(\kappa_1 + \kappa_2) + m_2^*\,\kappa_1/(\kappa_1 + \kappa_2)$. The fold change $r^* = m_2^*/m_1^*$ involves all ten parameters.

**Stage-independent kinetics.** Suppose $\nu_i = \nu$, $\delta_i = \delta$, $\lambda_i = \lambda$, $\gamma_i = \gamma$ for $i = 1,2$, and write $a = \lambda + \gamma$. Then

$$r^* = \frac{2(\delta + \kappa_1)(a + \kappa_1) + \kappa_2(a + \kappa_2)}{\kappa_1(a + \kappa_1) + (\delta + \kappa_2)(a + \kappa_2)}.$$

1. **Full range.** For every $C > 0$ there are admissible parameters with $r^* = C$: doubling the gene dosage does not constrain the fold change.
2. **Dependence on $\kappa_1$.** As $\kappa_1$ increases from $0$ to $\infty$, $r^*$ increases from a value below $2$ to a unique maximum and then decreases to $2$; moreover $r^* > 2$ iff $\kappa_1 > \kappa_2 + \dfrac{\kappa_2(\kappa_2 + a)}{2\delta}$.
3. **Dependence on $\kappa_2$.** As $\kappa_2$ increases from $0$ to $\infty$, $r^*$ decreases from a value above $2$ to a unique minimum and then increases to $1$; moreover $r^* < 1$ iff $\kappa_2 > a + 2\kappa_1 + \dfrac{\kappa_1(a + \kappa_1)}{\delta}$.
4. If $\kappa_1 \le \kappa_2$, then $r^*$ is bounded above by a constant strictly less than $2$.

## Expansion

Writing the master equation for the joint process (stage, promoter states, mRNA count) and taking first moments gives a closed linear system: in each stage the mean obeys $\dot m = \nu\,\mathbb E[\text{active copies}] - \delta m$, entering $S_2$ preserves $m$, and leaving $S_2$ halves it. Solving the stationary equations, with the promoter reset to OFF at each stage start (which introduces the factors $\lambda_i + \gamma_i + \kappa_i$), yields $m_1^*, m_2^*$; second moments follow the same way. With stage-independent kinetics, the threshold conditions in items 2–3 are equivalent to the polynomial inequalities $2\delta(a + \kappa_1) > 2\delta(a + \kappa_2) + \kappa_2(a + \kappa_2)$ and $(2\delta + \kappa_1)(a + \kappa_1) < \delta(a + \kappa_2)$ obtained by cross-multiplying. The limits follow by comparing leading terms: $r^* \to 2$ as $\kappa_1 \to \infty$ and $r^* \to 1$ as $\kappa_2 \to \infty$. Item 1 is shown by explicit parameter choices on the ranges $C \le 1$, $(1, 3/2]$, $(3/2, 2)$, $C \ge 2$; for instance $C \le 1$ is attained with $a = \kappa_1$, $\kappa_2 = 4\kappa_1/C$ and a suitable $\delta > 0$. The OFF-reset at stage boundaries and partitioning at division are what decouple the observed ratio from the gene copy number.

## Sources

- Q. Sun, F. Jiao, G. Lin, J. Yu, M. Tang, "The nonlinear dynamics and fluctuations of mRNA levels in cell cycle coupled transcription", *PLoS Computational Biology* (2019), Results (model assumptions i–v, Theorems 1–4, Eqs. (30)–(32), (42)–(47)), <https://doi.org/10.1371/journal.pcbi.1007017> (PMC6508750).
