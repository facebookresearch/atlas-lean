# Acid-mediated tumour invasion with two cooperating phenotypes

The **two-phenotype Gatenby–Gawlinski model** describes, on a one-dimensional tissue slice $x \in [0, 1]$ with zero-flux boundaries, the nondimensional densities of stroma $S$, acid-producing tumour cells $T_A$, matrix-degrading tumour cells $T_M$, lactic acid $L$ and extracellular matrix $M$:

$$\begin{aligned}
\partial_t S &= S(1 - S) - \delta S L, \\
\partial_t T_A &= \rho_T T_A (1 - c_S S - T_A - c_{M,A} T_M) + \Delta_T\, \partial_x\big[(1 - M)\, \partial_x T_A\big], \\
\partial_t T_M &= \rho_T T_M (1 - c_S S - c_{A,M} T_A - T_M) + \Delta_T\, \partial_x\big[(1 - M)\, \partial_x T_M\big], \\
\partial_t L &= \rho_L (T_A - L) + \partial_x^2 L, \\
\partial_t M &= -\kappa\, T_M M,
\end{aligned}$$

with positive parameters $\delta$ (acid toxicity to stroma), $\rho_T, \rho_L, \Delta_T, \kappa$, and competition coefficients $c_S > 1$ (stroma on tumour), $c_{M,A}, c_{A,M} \ge 0$ (between the phenotypes). Stroma is a biological barrier (it suppresses tumour growth and is removed only by acid, produced only by $T_A$). Matrix is a physical barrier (it blocks motility through the factor $1 - M$ and is removed only by $T_M$).

**Homogeneous steady states.** Besides healthy tissue $\mathrm{SS0} = (1, 0, 0, 0, M^*)$ with arbitrary $M^*$, the relevant tumour states are
- $\mathrm{SS1} = (0, 1, 0, 1, M^*)$: acid producers only, matrix intact;
- $\mathrm{SS2} = (0, 0, 1, 0, 0)$: matrix degraders only;
- $\mathrm{SS3} = \big(0,\ T_A^*,\ T_M^*,\ T_A^*,\ 0\big)$: coexistence of both phenotypes with stroma and matrix eradicated. Positive solutions $(T_A^*, T_M^*) \in (0, \infty)^2$ to the linear system $T_A + c_{M,A} T_M = 1$, $c_{A,M} T_A + T_M = 1$ exist in three cases:
  - if $c_{M,A} < 1$ and $c_{A,M} < 1$, or if $c_{M,A} > 1$ and $c_{A,M} > 1$, there is a unique positive coexistence state $T_A^* = \dfrac{1 - c_{M,A}}{1 - c_{M,A} c_{A,M}}$, $T_M^* = \dfrac{1 - c_{A,M}}{1 - c_{M,A} c_{A,M}}$;
  - if $c_{M,A} = c_{A,M} = 1$, the fractions are $0/0$ and the coexistence equilibria form the open segment $T_A^* + T_M^* = 1$ with $T_A^*, T_M^* > 0$;
  - otherwise (when $c_{M,A}$ and $c_{A,M}$ lie on opposite sides of $1$, or exactly one equals $1$), no strictly positive coexistence state exists.

**Linear stability** (spatially homogeneous perturbations). Every state with $M^* > 0$ has a zero eigenvalue in the $M$ direction, since without $T_M$ any matrix level is stationary; hence linear stability of such states is at best neutral along $M$ rather than strictly asymptotically stable. At $\mathrm{SS1}$ the remaining four eigenvalues are $1 - \delta$ (stroma), $\rho_T(1 - c_{A,M})$ (invasion by $T_M$), $-\rho_T$ and $-\rho_L$, so all four transverse eigenvalues are negative exactly when $\delta > 1$ and $c_{A,M} > 1$. When $\mathrm{SS3}$ exists with $c_{M,A}, c_{A,M} \ne 1$, the stroma eigenvalue is $1 - \delta T_A^*$, the matrix eigenvalue is $-\kappa T_M^* < 0$, and the $(T_A, T_M)$ block is the Lotka–Volterra competition Jacobian, which has both eigenvalues negative when $c_{A,M} < 1$ and $c_{M,A} < 1$ and is a saddle when $c_{A,M} > 1$ and $c_{M,A} > 1$; thus $\mathrm{SS3}$ is linearly asymptotically stable exactly when $c_{A,M} < 1$, $c_{M,A} < 1$ and $\delta T_A^* > 1$ (along the singular line $c_{A,M} = c_{M,A} = 1$ there is an additional zero eigenvalue along $T_A + T_M = 1$). $\mathrm{SS2}$ is unstable to stroma regrowth (eigenvalue $1$), and for the parameter ranges studied the mixed states with stroma are unstable. Hence an invading front can only connect healthy tissue to $\mathrm{SS1}$ or $\mathrm{SS3}$.

This corrects two expressions of the source as printed. Section 3 lists $\mathrm{SS3}$ as $\big(0, \frac{1-c_{M,A}}{1-c_{M,A}c_{A,M}}, \frac{1-c_{M,A}}{1-c_{M,A}c_{A,M}}, \frac{1-c_{M,A}}{1-c_{M,A}c_{A,M}}, 0\big)$, with the same fraction for $T_M^*$ as for $T_A^*$; but at $S = 0$ the $T_M$ equation (10) requires $c_{A,M}T_A^* + T_M^* = 1$, so $T_M^* = 1 - c_{A,M}\frac{1-c_{M,A}}{1-c_{M,A}c_{A,M}} = \frac{1-c_{A,M}}{1-c_{M,A}c_{A,M}}$, which is also the value behind the source's own Table 2 matrix eigenvalue $\frac{\kappa(1-c_{A,M})}{c_{A,M}c_{M,A}-1} = -\kappa T_M^*$. Table 2 (Appendix A2) prints the $\mathrm{SS3}$ stroma eigenvalue as $\frac{\rho_T(1 + c_{M,A}\delta - c_{A,M}c_{M,A} - \delta)}{1 - c_{A,M}c_{M,A}}$; but the stroma equation (8), $\partial_t S = S(1-S) - \delta SL$, carries no factor $\rho_T$, and its derivative in $S$ at $S = 0$, $L = T_A^*$ is $1 - \delta T_A^* = \frac{1 + c_{M,A}\delta - c_{A,M}c_{M,A} - \delta}{1 - c_{A,M}c_{M,A}}$. Since $\rho_T > 0$ the sign, and so the stability conclusion, is the same.

## Depends on

This node has no prerequisites.

## Proof depends on

None beyond the statement prerequisites; this page is a definition.

## Expansion

Away from the front, $S$, $L$ and $M$ are slaved, and the tumour block reduces to two-species Lotka–Volterra competition with identical growth rates and carrying capacities. Weak mutual competition ($c_{A,M}, c_{M,A} < 1$) gives stable coexistence. $c_{A,M} > 1 > c_{M,A}$ lets acid producers exclude matrix degraders, and the reverse gives exclusion of acid producers. When both exceed one the coexistence state is a saddle whose stable manifold separates the exclusion basins, so the outcome depends on initial conditions and is structurally unstable along $c_{A,M} = c_{M,A}$. Biologically, neither phenotype invades alone. Without $T_M$ the front stalls once it reaches intact matrix, since without $T_M$ every matrix level is stationary (the zero eigenvalue). Without $T_A$ the stroma is never cleared and suppresses growth ($c_S > 1$). Sustained invasion at realistic speeds therefore needs the coexistence state $\mathrm{SS3}$ behind the front, or a transient $T_A$-dominated front.

## Sources

- M. A. R. Strobl, A. L. Krause, M. Damaghi, R. Gillies, A. R. A. Anderson and P. K. Maini, "Mix and match: phenotypic coexistence as a key facilitator of cancer invasion", Bulletin of Mathematical Biology 82 (2020), 15, Section 2 (Eqs. (1)–(12)), Section 3 (steady states SS0–SS6) and Appendix A2 (Table 2), <https://doi.org/10.1007/s11538-019-00675-0> (PMC6968991).
