# Well-posedness of nonlocal age- and space-structured epidemic models

Let $\Omega \subset \mathbb R^2$ be a bounded domain with smooth boundary, $0 < a_{\max} < \infty$ the maximal age, $\mathcal I = (0, a_{\max})$, $H = L^2(\Omega)^n$ and $V = H^1(\Omega)^n$. A vector $y(t, a, x) \in \mathbb R^n$ of epidemic compartments (for instance $S, V, I, R$) evolves by

$$ (\partial_t + \partial_a) y + L(a,x)\, y + \Lambda(a,x,y)\, y + K(u)\, y = \sigma(a) \Delta y, \qquad y(0,\cdot,\cdot) = y_0, \qquad y(t,0,x) = \int_0^{a_{\max}} \beta(\alpha,x)\, y(t,\alpha,x)\, d\alpha, $$

with homogeneous Neumann conditions on $\partial\Omega$. Here $L$ collects the linear transitions (recovery, waning, death), $\sigma$ is a diagonal matrix of age-dependent diffusion rates, the renewal condition at $a = 0$ encodes births with fertility matrix $\beta$, $K(u)$ is a control term linear in a vaccination rate $u$, and the infection operator is nonlocal in age and space:

$$ \Lambda(a,x,y)^{hi} = \int_0^{a_{\max}} \int_\Omega k^{hij}(a,\alpha,x,\xi)\, y_j(\alpha,\xi)\, d\xi\, d\alpha, $$

where $k^{hij}$ is the rate at which infectives of type $j$ at age $\alpha$ and position $\xi$ move susceptibles of type $i$ at $(a,x)$ into class $h$.

**Linear problem.** Assume $\beta \in C(\bar{\mathcal I}, L^\infty(\Omega)^{n\times n})$, $L \in C(\bar{\mathcal I}, L^\infty(\Omega))$ with entries bounded away from zero, $\sigma \in C(\bar{\mathcal I}, \mathbb R^{n\times n})$ diagonal with entries bounded away from zero, $y_0 \in L^2(\mathcal I, H)$ and a source $f \in L^2((0,T)\times\mathcal I, V')$. Then the birth flux $B(t) = y(t, 0, \cdot)$ is the unique solution in $L^2((0,T), H)$ of a Volterra equation, and the linear problem $(\partial_t + \partial_a) y + L y - \sigma\Delta y = f$ with this renewal condition has a unique weak solution $y \in L^2((0,T)\times\mathcal I, V) \cap C([0,T], L^2(\mathcal I, H))$ with $(\partial_t + \partial_a) y \in L^2((0,T)\times\mathcal I, V')$, bounded by $\|y_0\|$ and $\|f\|$.

**Nonlinear problem.** If in addition $K(u)$ is linear in a bounded control $0 \le u \le \bar u$ and the kernel $k$ makes $\Lambda$ satisfy $\|\Lambda(y_1) y_2\| \le c(k) \|y_1\| \|y_2\|$ in $L^2(\mathcal I, H)$, then there is $T^* \le T$, depending only on $\bar u$ and the data, such that the full model has a unique weak solution on $(0, T^*)$ in the same space, with an energy estimate.

## Expansion

Along each characteristic $t - a = t_0$ (one birth cohort), the linear equation is a parabolic problem in $x$ alone, solved by evolution operators $U(t,s)$ from standard parabolic theory. Gluing cohorts, started either from $y_0$ (for $t_0 < 0$) or from the birth flux $B(t_0)$ (for $t_0 \ge 0$), gives the solution with $B$ prescribed; integrating that representation against the fertility $\beta$ turns the renewal condition into a Volterra equation for $B$, solvable by Prüss's theory. The lack of a time derivative and an age derivative separately (only $\partial_t + \partial_a$ is controlled) is handled by Fubini over characteristics. The nonlinear problem is then a Banach fixed point for the map that freezes $\Lambda(y)$ and $K(u)$, contractive on a short interval because $\Lambda$ is bilinear and bounded. The SVIR model with vaccination, waning vaccine and natural immunity, and newborns entering $S$ is a special case. The results are Theorems 2.11, 2.13 and 2.15 of the source.

## Sources

- B. Azmi and N. Schlosser, *Optimal Control of General Nonlocal Epidemic Models with Age and Space Structure*, arXiv:2503.01466 (2025), Theorems 2.11, 2.13, 2.15. <https://doi.org/10.48550/arXiv.2503.01466> Published version: Journal of Differential Equations 464 (2026) 114250, <https://doi.org/10.1016/j.jde.2026.114250>.
