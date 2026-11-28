# IAST with equal Langmuir capacities gives competitive Langmuir adsorption

If every pure component follows a Langmuir isotherm with the same saturation loading $M$, IAST gives $N_i = MK_if_i/(1+\sum_jK_jf_j)$.

Let $n \ge 2$ components have pure-component Langmuir isotherms $L_i(f) = MK_if/(1+K_if)$ in the fugacity $f$, with a
common saturation loading $M > 0$ and constants $K_i > 0$, all at one temperature on one adsorbent. For partial
fugacities $f_i > 0$ of the bulk mixture (partial pressures for an ideal-gas bulk), ideal adsorbed solution theory has
a unique solution, with loadings

$$
N_i = M\,\frac{K_if_i}{1 + \sum_{j=1}^n K_jf_j} \qquad (i = 1, \dots, n),
$$

the competitive (extended) Langmuir model. In particular the fugacity-normalized adsorption selectivity is
$K_i/K_j$, independent of composition and pressure. For arbitrary unequal capacities the conclusion fails in general.

## Context

Graduate level. This is the exactly solvable case of IAST, used to test IAST solvers and to read Langmuir affinity ratios as selectivities.

## Depends on

- [Ideal adsorbed solution theory](ideal-adsorbed-solution-theory.md)
- [Langmuir isotherm](langmuir-isotherm.md)
- [Adsorption selectivity](adsorption-selectivity.md)

## Proof depends on

- [Reduced spreading pressure](reduced-spreading-pressure.md)

## Expansion

For a Langmuir isotherm the integrand of the reduced spreading pressure is $MK_i/(1+K_if)$, so
$\Pi_i(P) = M\ln(1+K_iP)$, and equal spreading pressures force $K_iP_i^0 = s$ for a common $s > 0$. Then
$x_i = f_i/P_i^0 = K_if_i/s$, and $\sum_ix_i = 1$ gives $s = \sum_jK_jf_j$, so the solution exists and is unique.
Each $q_i^0(P_i^0) = Ms/(1+s)$, so $q_t = Ms/(1+s)$ and $N_i = x_iq_t = MK_if_i/(1+s)$.

## Sources

- C. M. Simon, B. Smit and M. Haranczyk, *pyIAST documentation*, sections "Competitive Langmuir adsorption" and "ModelIsotherm" (model list and `spreading_pressure`), [pyiast.readthedocs.io](https://pyiast.readthedocs.io/en/latest/), section "Competitive Langmuir adsorption".
- R. Krishna and J. M. van Baten, "How Reliable Is the Ideal Adsorbed Solution Theory for the Estimation of Mixture Separation Selectivities in Microporous Crystalline Adsorbents?", *ACS Omega* 6, 15499–15513 (2021), [doi.org](https://doi.org/10.1021/acsomega.1c02136), Eqns (1)–(7).
