# Competitive exclusion in a two-variant SIRS model

**Model.** Let $S, I_1, I_2, R \ge 0$ be susceptible, variant-1 infected, variant-2 infected and recovered (immune) numbers, with recruitment $\Lambda > 0$, natural removal rates $d_S, d_{I_1}, d_{I_2}, d_R > 0$, transmission coefficients $\beta_1, \beta_2 > 0$, recovery rates $\gamma_1,\gamma_2 \ge 0$, detection-and-isolation rates $\rho_1, \rho_2 \ge 0$ and waning rate $\delta \ge 0$:

$$\begin{aligned}
S' &= \Lambda - \beta_1 S I_1 - \beta_2 S I_2 - d_S S + \delta R,\\
I_1' &= \beta_1 S I_1 - (\gamma_1 + \rho_1 + d_{I_1}) I_1,\\
I_2' &= \beta_2 S I_2 - (\gamma_2 + \rho_2 + d_{I_2}) I_2,\\
R' &= (\gamma_1+\rho_1) I_1 + (\gamma_2+\rho_2) I_2 - (d_R + \delta) R .
\end{aligned}$$

Co-infection is ignored and both variants feed a single immune class. The disease-free equilibrium is $P_0 = (\Lambda/d_S, 0, 0, 0)$. Define the variant-specific reproduction numbers and $R_0$:

$$R_{0i} = \frac{\beta_i}{\gamma_i + \rho_i + d_{I_i}}\cdot\frac{\Lambda}{d_S}\quad (i=1,2), \qquad R_0 = \max\{R_{01}, R_{02}\}.$$

The single-variant equilibrium $P_1 = (\bar S, \bar I_1, 0, \bar R)$, with $\bar S = (\gamma_1 + \rho_1 + d_{I_1})/\beta_1$, lies in the nonnegative orthant iff $R_{01} \ge 1$ (and equals $P_0$ when $R_{01}=1$); symmetrically for $P_2 = (\bar{\bar S}, 0, \bar{\bar I}_2, \bar{\bar R})$.

**Theorem.** On the positively invariant feasible region:
1. If $R_0 < 1$, $P_0$ is the only equilibrium and it is asymptotically stable.
2. If $R_0 > 1$, $P_0$ is unstable, and
   - if $R_{02} < 1 < R_{01}$, $P_1$ is the asymptotically stable equilibrium and $P_2$ is infeasible; if $1 < R_{02} < R_{01}$, both exist, $P_1$ is asymptotically stable and $P_2$ is unstable in the direction pointing into the interior;
   - symmetrically with the roles of the variants exchanged when $R_{02} > R_{01}$;
   - if $R_{01} = R_{02} > 1$, a line segment of positive coexistence equilibria joins $P_1$ and $P_2$; each is neutrally stable along the segment and asymptotically stable transversally.

In particular, a positive (coexistence) equilibrium exists only if $R_{01} = R_{02}$.

## Expansion

At a coexistence equilibrium both $I_i' = 0$ with $I_i > 0$ force $\beta_i S^* = \gamma_i + \rho_i + d_{I_i}$ for $i=1,2$, so $S^*$ must equal both $\bar S$ and $\bar{\bar S}$, which happens iff $R_{01}=R_{02}$; the remaining equilibrium equations are then a single linear relation in $(I_1^*, I_2^*)$, giving a segment. Stability of $P_0$ follows from the next-generation matrix, which is diagonal with entries $R_{01}, R_{02}$. At $P_1$, the eigenvalue in the $I_2$ direction is $\beta_2\bar S - (\gamma_2+\rho_2+d_{I_2}) = (\gamma_2+\rho_2+d_{I_2})(R_{02}/R_{01} - 1)$, negative iff $R_{02} < R_{01}$; the remaining eigenvalues come from the single-variant SIRS subsystem, handled by Routh–Hurwitz. Over a finite epidemic wave the excluded variant can persist at appreciable levels for months, so observed "coexistence" in surveillance data is a transient, not an asymptotic, phenomenon.

## Depends on

- [Basic reproduction number of the next-generation matrix](../../next-generation-matrix-and-the-basic-reproductio/r0.md)

## Sources

- A. S. Ciupeanu, M. Varughese, W. C. Roda, D. Han, Q. Cheng, M. Y. Li, "Mathematical modeling of the dynamics of COVID-19 variants of concern: asymptotic and finite-time perspectives", Infectious Disease Modelling 7(4) (2022) 581–596, model (1), Equations 3–6 and Theorem 1, <https://doi.org/10.1016/j.idm.2022.08.004>, PMCID PMC9454204.
- V. Andreasen, J. Lin, S. A. Levin, "The dynamics of cocirculating influenza strains conferring partial cross-immunity", Journal of Mathematical Biology 35 (1997) 825–842, <https://doi.org/10.1007/s002850050079>.
