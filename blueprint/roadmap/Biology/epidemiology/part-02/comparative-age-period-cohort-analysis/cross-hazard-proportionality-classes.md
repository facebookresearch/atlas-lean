# Cross-hazard proportionality classes in age-period-cohort models

**Setting.** A Lexis diagram has age groups $a \in \{1,\dots,A\}$ and calendar periods $p \in \{1,\dots,P\}$ with $A, P \ge 2$; the birth cohort of cell $(a,p)$ is $c = p - a$. For strata $g = 1,\dots,G$ with hazard rates $\lambda^{(g)}(a,p) > 0$ following age-period-cohort models

$$\log \lambda^{(g)}(a,p) = \mu_g + \alpha_g(a) + \pi_g(p) + \gamma_g(p-a),$$

the cross-hazard rate ratio of strata $j$ and $k$ is $RR^{j:k}(a,p) = \lambda^{(j)}(a,p)/\lambda^{(k)}(a,p)$. The pair is called

- **PH-L** (longitudinal) if $RR^{j:k}$ depends on $(a,p)$ only through the cohort $p-a$ (constant along diagonals);
- **PH-T** (time) if it depends only on the age $a$ (constant across periods);
- **PH-X** (cross-sectional) if it depends only on the period $p$ (constant across age groups);
- **PH-A** (absolute) if it is constant on the whole diagram;
- **N-PH** if none of PH-L, PH-T, PH-X holds.

**Theorem.** If any two of PH-L, PH-T, PH-X hold for a pair of strata, then PH-A holds (hence so does the third). Consequently each pair falls in exactly one of the five classes PH-L only, PH-T only, PH-X only, PH-A, N-PH. Under PH-A, $RR^{j:k} = e^{\mu_j - \mu_k}$ in the parametrization where the deviation terms of $j$ and $k$ coincide.

**Consequences for estimable functions.** In the extended age-period-cohort parametrization with net drift and local drifts:
- under PH-T the strata share the net drift, the longitudinal and cross-sectional age-curve ratios coincide, $\mathrm{LongAge}^{(j)}(a)/\mathrm{LongAge}^{(k)}(a) = \mathrm{CrossAge}^{(j)}(a)/\mathrm{CrossAge}^{(k)}(a)$, and the local-drift curves are identical;
- under PH-X the local-drift curves are parallel, differing by the difference of net drifts;
- under PH-L and N-PH the local-drift curves are not parallel in general.

## Expansion

Let $\delta(a,p) = \log RR^{j:k}(a,p)$, a function on the grid. Case PH-L and PH-T: $\delta(a,p) = \phi(p-a) = \psi(a)$. Fixing $a$ and letting $p$ range over $\{1,\dots,P\}$ shows $\phi$ is constant on the cohort window $\{1-a,\dots,P-a\}$. Windows for consecutive ages $a$ and $a+1$ overlap in $P-1 \ge 1$ cohorts, so $\phi$ is constant on all cohorts and $\delta$ is constant. Case PH-L and PH-X: the same argument with $p$ fixed and $a$ varying, using $A \ge 2$. Case PH-T and PH-X: $\psi(a) = \chi(p)$ for all $a,p$ forces both to equal a common constant. The statement uses only the grid geometry, not the parametric form; the parametric form identifies which estimable functions inherit the constraint. For example, PH-T makes the fitted temporal trends of the strata proportional, which equalizes their net drifts and, since local drifts add cohort-deviation slopes to the net drift, makes the local drifts identical.

## Sources

- P. S. Rosenberg, A. Miranda-Filho, D. C. Whiteman, "Comparative age-period-cohort analysis", BMC Medical Research Methodology 23 (2023) 238, Methods (four canonical proportionalities, Corollaries 1–2, Table 1), <https://doi.org/10.1186/s12874-023-02039-8>, PMCID PMC10585891.
- T. R. Holford, "The estimation of age, period and cohort effects for vital rates", Biometrics 39 (1983) 311–324, <https://doi.org/10.2307/2531004>.
