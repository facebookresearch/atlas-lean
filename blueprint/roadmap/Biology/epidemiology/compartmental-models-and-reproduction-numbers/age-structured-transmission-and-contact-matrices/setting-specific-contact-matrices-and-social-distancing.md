# Setting-specific contact matrices and the reproduction number under social distancing

**Setting.** Let the age-group contact matrix be a sum over social settings,

$$C = \sum_{s \in \mathcal S} C^{(s)}, \qquad \mathcal S = \{\text{household}, \text{school}, \text{work}, \text{transport}, \text{leisure}, \text{other}\},$$

with nonnegative matrices $C^{(s)} = (c^{(s)}_{ij})$, and let the [age-structured next-generation matrix](age-structured-force-of-infection-and-next-generation-matrix.md) be $K(C) = A\, C\, B$ with fixed nonnegative diagonal matrices $A = \mathrm{diag}(q\sigma_i N_i)$ and $B = \mathrm{diag}(D_j / N_j)$, so that $R(C) = \rho(K(C))$. A social-distancing scenario is a modified matrix

$$C' = \sum_{s} \big(C^{(s)} - \Delta^{(s)}\big) \quad\text{or more generally}\quad 0 \le C' \le C \ \text{entrywise},$$

for example: school closure removes $C^{(\text{school})}$; a fraction $f$ of workers staying home scales work and transport contacts of working-age adults by $1 - f$; isolation of seniors scales the rows and columns of the oldest group by $1 - g$; closure of leisure activities removes or halves $C^{(\text{leisure})}$. (Interventions that move contacts into households, such as telework, add to $C^{(\text{household})}$ and are not entrywise reductions.)

**Statements.**

1. *Monotonicity.* If $0 \le C' \le C$ entrywise then $R(C') \le R(C)$.
2. *Uniform reduction.* If every setting is reduced by the same factor, $C' = (1 - \epsilon)\, C$ with $\epsilon \in [0,1]$, then $R(C') = (1 - \epsilon)\, R(C)$; in particular the epidemic is controlled ($R(C') < 1$) iff $\epsilon > 1 - 1/R(C)$.
3. *Partial reductions.* If the reduction factors differ across settings, $C' = \sum_s (1 - \epsilon_s)\, C^{(s)}$, then

$$\big(1 - \max_s \epsilon_s\big)\, R(C) \le R(C') \le \big(1 - \min_s \epsilon_s\big)\, R(C),$$

so a strategy that leaves any setting untouched cannot lower $R$ by more than that setting allows: if setting $s_0$ is unreduced, $R(C') \ge \rho\big(K(C^{(s_0)})\big)$.

## Depends on

- [Age-structured force of infection and next-generation matrix](age-structured-force-of-infection-and-next-generation-matrix.md)
- [Basic reproduction number of the next-generation matrix](../../next-generation-matrix-and-the-basic-reproductio/r0.md)

## Expansion

All three statements follow from the monotonicity of the spectral radius on nonnegative matrices: if $0 \le M' \le M$ entrywise then $\rho(M') \le \rho(M)$ (Perron–Frobenius; for example via $\rho(M) = \lim_k \|M^k\|^{1/k}$ with a monotone norm). Since $A, B \ge 0$ are diagonal, $0 \le C' \le C$ implies $0 \le A C' B \le A C B$, giving 1. Statement 2 is homogeneity, $\rho(tM) = t\rho(M)$ for $t \ge 0$. For 3, $(1 - \max_s\epsilon_s) C \le C' \le (1 - \min_s \epsilon_s) C$ entrywise, then apply 1 and 2; the last bound uses $C' \ge C^{(s_0)}$. In the Île-de-France study these reconstructions of the contact matrices, informed by mobility data, gave an $81\%$ reduction in the average number of contacts during lockdown and a drop of the reproductive number from $3.18$ to $0.68$; exit strategies were then compared as alternative partial reductions $C'$.

## Sources

- L. Di Domenico, G. Pullano, C. E. Sabbatini, P.-Y. Boëlle, V. Colizza, "Impact of lockdown on COVID-19 epidemic in Île-de-France and possible exit strategies", BMC Medicine (2020), Methods ("Mixing", "Social distancing interventions", Table 1) and Results ("Reproduction number, start of the epidemic, population infected"), <https://doi.org/10.1186/s12916-020-01698-4> (PMC7391016).
