# Mosquito reproduction number and density-regulated equilibrium

**Setting.** In the [stage-structured mosquito model](stage-structured-mosquito-model-with-density-dependent-larval-mortality.md), define the *effective mosquito reproduction number* at larval densities $(E, L)$ as the expected number of adult females produced by one adult female over her lifetime when larval death rates are frozen at $\mu_E(E,L)$, $\mu_L(E,L)$:

$$R_{\mathrm{eff}}(E,L) = \frac{\beta}{2\mu_M}\cdot\frac{1}{1 + d_E\,\mu_E(E,L)}\cdot\frac{1}{1 + d_L\,\mu_L(E,L)}\cdot\frac{1}{1 + d_P\,\mu_P},$$

and the *basic mosquito reproduction number* $R_0 = R_{\mathrm{eff}}(0,0)$, obtained with the low-density rates $\mu_E^0, \mu_L^0$.

**Proposition.**

1. $R_{\mathrm{eff}}(E, L)$ depends on $(E,L)$ only through $x = E + L$, is strictly decreasing in $x$, and tends to $0$ as $x \to \infty$.
2. If $R_0 > 1$ there is a unique total larval density $x^\ast > 0$ with $R_{\mathrm{eff}} = 1$; if $R_0 \le 1$ there is none.
3. Every positive equilibrium $(E^\ast, L^\ast, P^\ast, M^\ast)$ of the model satisfies $R_{\mathrm{eff}}(E^\ast, L^\ast) = 1$, so a positive equilibrium requires $R_0 > 1$. At such an equilibrium $P^\ast = 2 d_P\,\mu_M M^\ast$, $L^\ast = d_L (1 + d_P \mu_P) P^\ast / d_P$ and $E^\ast = d_E (1 + d_L \mu_L(E^\ast,L^\ast)) L^\ast / d_L$.
4. Positive equilibrium abundances scale linearly with carrying capacity: if $(E^\ast, L^\ast, P^\ast, M^\ast)$ is an equilibrium for $K$, then $c\,(E^\ast, L^\ast, P^\ast, M^\ast)$ is an equilibrium for $cK$, $c > 0$.

## Depends on

- [Stage-structured mosquito model with density-dependent larval mortality](stage-structured-mosquito-model-with-density-dependent-larval-mortality.md)
- [Oviposition rate from the gonotrophic cycle](oviposition-rate-from-the-gonotrophic-cycle.md)

## Expansion

A female lays $\beta$ eggs per day for a mean of $1/\mu_M$ days; an egg becomes an adult with probability $s_E s_L s_P$ (product of the stage survival probabilities) and is female with probability $1/2$, which gives the formula. (1) holds because both larval death rates are increasing affine functions of $x$ and $\mu_E^0, \mu_L^0 > 0$; (2) follows by continuity and monotonicity. For (3), setting the derivatives to zero and solving backwards from the adult equation gives the stated relations; substituting into the egg equation yields $\beta M^\ast = E^\ast (1 + d_E \mu_E)/d_E$, which after the substitutions is exactly $R_{\mathrm{eff}}(E^\ast, L^\ast) = 1$. For (4), the rates depend on $(E,L)$ only through $(E+L)/K$, and the system is otherwise linear. The source stresses that $R_0$ is an idealization: density dependence is always present, so the realized $R_{\mathrm{eff}}(t)$ fluctuates around one as seasonal rainfall moves $K(t)$.

## Sources

- M. T. White, J. T. Griffin, T. S. Churcher, N. M. Ferguson, M.-G. Basáñez, A. C. Ghani, "Modelling the impact of vector control interventions on *Anopheles gambiae* population dynamics", Parasites & Vectors 4 (2011) 153, Methods, "Mosquito growth rate and reproduction number", Eqs. (4)–(6), <https://doi.org/10.1186/1756-3305-4-153> (PMC3158753).
