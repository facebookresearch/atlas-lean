# Specific flux maximization as enzyme cost minimization over metabolites

**Setting.** A metabolic network has stoichiometric matrix $N$, internal metabolite concentrations $x_I$, external concentrations $x_E$ and reactions $j=1,\dots,m$ with rates $v_j=e_jf_j(x_I;x_E)$, where $e_j$ is the enzyme concentration and $f_j$ the enzyme-specific rate law. For a fixed output reaction $r$, the specific flux is $v_r/e_T$ with total enzyme $e_T=\sum_je_j$.

**Reduction (Eqs. 6–7).** Maximizing $v_r/e_T$ at steady state is equivalent, after normalizing $v_r=1$, to

$$\min_{x_I,e}\Bigl\{\sum_je_j\ \Big|\ Nv=0,\ v_r=1\Bigr\}=\min_{x_I}\Bigl\{\sum_j\frac{v_j}{f_j(x_I;x_E)}\ \Big|\ Nv=0,\ v_r=1\Bigr\},$$

so the enzyme concentrations drop out and only metabolite concentrations remain as decision variables.

**Allocation within an elementary flux mode (Eqs. 8–10).** Optimal flux profiles are elementary flux modes (EFMs). Within an EFM with flux vector $(V_1,\dots,V_m)$, the optimal metabolite state minimizes

$$O(x_I)=\sum_{j=1}^m\frac{V_j}{f_j(x_I;x_E)},$$

which is strictly convex for a broad class of rate laws, so the minimizer $x_I^o$ is unique and determined by $x_E$. The optimal enzyme levels are $e_j^o=V_j/f_j(x_I^o;x_E)$, up to a common scale fixed by the total enzyme budget.

## Expansion

If $(x_I,e)$ achieves specific flux $v_r/e_T$ then scaling all $e_j$ by a constant scales every flux and $e_T$ alike, so the specific flux depends only on direction; fixing $v_r=1$ and minimizing total enzyme is the same problem. Substituting $e_j=v_j/f_j$ removes $e$. Unlike flux balance analysis this optimization is kinetic: the variables are concentrations, and the optimum makes each enzyme as saturated as possible, i.e. maximizes all $f_j$ jointly, weighted by the EFM fluxes. The optimality conditions are $\partial O/\partial x_i=0$ for every internal metabolite (Eq. 11).

## Sources

- R. Planqué, J. Hulshof, B. Teusink, J. C. Hendriks, F. J. Bruggeman, "Maintaining maximal metabolic flux by gene expression control", PLoS Computational Biology 14 (2018) e1006412. <https://doi.org/10.1371/journal.pcbi.1006412>, PMCID PMC6168163. Steps 1–2 of the construction, Eqs. (4)–(11).
