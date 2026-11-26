# The Fan graph is a transient amplifier of selection

**Definitions.** For death-Birth updating, a graph $G$ of size $N$ is a *transient amplifier of selection* if there is $r^* > 1$ with $\rho_G(r) < \rho_{K_N}(r)$ for $0 < r < 1$ and for $r > r^*$, and $\rho_G(r) > \rho_{K_N}(r)$ for $1 < r < r^*$; it is a *reducer of fixation* if $\rho_G(r) < \rho_{K_N}(r)$ for all $r \ne 1$.

**The Fan.** $F_{n,m}$ has one hub and $n \ge 2$ blades of $m \ge 2$ vertices each ($N = nm + 1$). Vertices on the same blade are joined by edges of weight $1$, and every blade vertex is joined to the hub by an edge of weight $\epsilon > 0$; there are no other edges. The Fan is isothermal exactly when $\epsilon = (m-1)/(nm-1)$.

**Theorem.** (i) Its effective population size is

$$N_{\mathrm{eff}} = N + \frac{\big(m-1-\epsilon(nm-1)\big)\big(m(m-1)(n-2) + \epsilon(nm^2+nm-4m+2) + 2\epsilon^2(nm-1)\big)}{(m-1+2\epsilon)\big(m(m-1) + \epsilon(nm+2m-1) + \epsilon^2(nm+1)\big)},$$

so the Fan amplifies weak selection for all $0 < \epsilon < (m-1)/(nm-1)$; as $\epsilon \to 0$, $N_{\mathrm{eff}} \to nm + n - 1$.

(ii) In the limit $\epsilon \to 0$, the fixation probability for arbitrary $r > 0$ is

$$\rho_{F_{n,m}}(r) = \frac{n(m-1)\,(1-r^{-1})\,(1-r^{-(m+1)})}{(mn+1)\,(1-r^{-(m-1)})\,(1-r^{-n(m+1)})}.$$

(iii) In this limit the Fan is a reducer of fixation for $n = 2$ and a transient amplifier of selection for every $n \ge 3$. The largest ratio $N_{\mathrm{eff}}/N$ is approached for $m = 2$, $\epsilon \to 0$ and then $n \to \infty$, where $N_{\mathrm{eff}}/N \to 3/2$; in that limit the Fan amplifies exactly for $1 < r < (1+\sqrt5)/2$.

## Depends on

- [Coalescence-time formula for weak-selection fixation under death-Birth updating](coalescence-time-formula-for-weak-selection-fixation-under-death-birth-updating.md)

## Expansion

(i) is obtained by solving the coalescence-time recursion on the three vertex classes (hub, same blade, different blades) and evaluating $N_{\mathrm{eff}} = \sum_i\pi_i\tau_i$; the sign of the numerator factor $m-1-\epsilon(nm-1)$ decides amplification. For (ii), when $\epsilon \to 0$ a blade is almost always replaced from within, so a blade quickly becomes monochromatic; the slow dynamics is then a birth-death chain on the number of mutant blades driven by rare hub-mediated events, which gives the product of geometric-series factors. Comparing (ii) with $\rho_{K_N}(r)$ shows a single crossing at some $r^* > 1$ when $n \ge 3$ and none when $n = 2$. The bounded amplification range is consistent with the companion result that death-Birth updating admits no amplifiers that work for all $r > 1$.

## Sources

- B. Allen, C. Sample, R. Jencks, J. Withers, P. Steinhagen, L. Brizuela, J. Kolodny, D. Parke, G. Lippner, Y. A. Dementieva, "Transient amplifiers of selection and reducers of fixation for death-Birth updating on graphs", PLoS Computational Biology 16 (2020) e1007529, Definition of transient amplifiers, Eqs. (14)–(15), Fig 3 and S1 Appendix, <https://doi.org/10.1371/journal.pcbi.1007529>, PMCID PMC6968840.
