# Specific flux maximization as enzyme cost minimization over metabolites

**Setting.** A metabolic network has stoichiometric matrix $N$, internal metabolite concentrations $x_I$, external concentrations $x_E$ and reactions $j=1,\dots,m$ with rates $v_j=e_jf_j(x_I;x_E)$, where $e_j$ is the enzyme concentration and $f_j$ the enzyme-specific rate law. For a fixed output reaction $r$, the specific flux is $v_r/e_T$ with total enzyme $e_T=\sum_je_j$.

**Reduction (Eqs. 6–7).** Maximizing $v_r/e_T$ at steady state is equivalent, after normalizing $v_r=1$, to

$$\min_{x_I,\,e \ge 0}\Bigl\{\sum_je_j\ \Big|\ Nv=0,\ v_r=1\Bigr\}=\min_{x_I,\,v}\Bigl\{\sum_j\frac{v_j}{f_j(x_I;x_E)}\ \Big|\ Nv=0,\ v_r=1,\ \frac{v_j}{f_j(x_I;x_E)} \ge 0\Bigr\},$$

so the enzyme concentrations drop out, while the metabolite concentrations and the fluxes remain as decision variables. The constraint $e_j = v_j/f_j \ge 0$ is needed: without it the right-hand minimum is $-\infty$ whenever some steady-state flux $w$ has $w_r = 0$ and $\sum_j w_j/f_j \ne 0$ (for example a reversible internal cycle).

**Allocation within an elementary flux mode (Eqs. 8–10).** Optimal flux profiles are elementary flux modes (EFMs). Within an EFM with flux vector $(V_1,\dots,V_m)$, the optimal metabolite state minimizes

$$O(x_I)=\sum_{j=1}^m\frac{V_j}{f_j(x_I;x_E)},$$

1. **Convexity and existence of a global optimum.** Under the thermodynamic kinetics (3), each $f_j(x_I; x_E)$ is a strictly positive, log-concave function of $x_I$ (or of the log-concentrations $\ln x_I$) on the feasible domain of $x_I > 0$ with $V_j f_j(x_I; x_E) > 0$ for all $j$ with $V_j \neq 0$, so $1/f_j$ is convex and $O(x_I)$ is convex on that domain. Assume this domain is nonempty and bounded (the source calls it "generally a convex and compact set"); it can be unbounded with an irreversible step ($K_{\mathrm{eq}} = 0$, e.g. $A \to m \to B$ where $m$ can grow without bound) or with a conserved moiety (e.g. a reversible cofactor cycle $A + m_1 \rightleftharpoons m_2$, $m_2 \rightleftharpoons m_1 + B$ whose feasible domain is an open cone along which $O$ strictly decreases), and in either case the infimum need not be attained. When the domain is nonempty and bounded, $O(x_I)$ blows up at its boundary and attains a global minimum, which is unique whenever $O$ is strictly convex.

## Expansion

If $(x_I,e)$ achieves specific flux $v_r/e_T$ then scaling all $e_j$ by a constant scales every flux and $e_T$ alike, so the specific flux depends only on direction; fixing $v_r=1$ and minimizing total enzyme is the same problem. Substituting $e_j=v_j/f_j$ removes $e$. Unlike flux balance analysis this optimization is kinetic: the variables are concentrations, and the optimum makes each enzyme as saturated as possible, i.e. maximizes all $f_j$ jointly, weighted by the EFM fluxes. The optimality conditions are $\partial O/\partial x_i=0$ for every internal metabolite (Eq. 11).

## Sources

- R. Planqué, J. Hulshof, B. Teusink, J. C. Hendriks, F. J. Bruggeman, "Maintaining maximal metabolic flux by gene expression control", PLoS Computational Biology 14 (2018) e1006412. <https://doi.org/10.1371/journal.pcbi.1006412>, PMCID PMC6168163. Steps 1–2 of the construction, Eqs. (4)–(11).
