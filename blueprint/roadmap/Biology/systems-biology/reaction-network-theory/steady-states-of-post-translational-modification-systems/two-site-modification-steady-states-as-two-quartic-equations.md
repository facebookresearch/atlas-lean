# Two-site modification steady states as two quartic equations

**Setting.** A substrate $S$ is modified at two sites in a fixed order by a forward enzyme $E$ and demodified in the reverse order by an enzyme $F$, giving three modforms $S_0, S_1, S_2$ ($S_i$ has $i$ modified sites). Each of the four reactions $S_0 \xrightarrow{E} S_1$, $S_1 \xrightarrow{E} S_2$, $S_1 \xrightarrow{F} S_0$, $S_2 \xrightarrow{F} S_1$ may follow any reasonable distributive mass-action mechanism built from substrate binding, intermediate complexes and product release; product rebinding is allowed. The linear framework summarizes the steady state of each mechanism by generalized parameters: for $S_i \xrightarrow{X} S_j$, reciprocal total generalized Michaelis–Menten constants $\kappa^X_{i,j}, \kappa^X_{j,i} \ge 0$ with

$$\kappa^X_{i,j}[X][S_i] + \kappa^X_{j,i}[X][S_j] = \sum_{S_i \to_X S_j} [Y^*],$$

the total steady-state concentration of that mechanism's intermediate complexes, and total generalized catalytic efficiencies $c^X_{i,j}, c^X_{j,i}$ giving the net rate contribution $c^X_{i,j}[X][S_i] - c^X_{j,i}[X][S_j]$. Irreversibility is imposed as $\kappa^X_{i,j} > 0$, $c^X_{i,j} > 0$, $\kappa^X_{j,i} \ge 0$, $c^X_{j,i} = 0$ for the forward direction of each reaction.

**Reduction.** Let $\alpha = c^E_{0,1}/c^F_{1,0}$, $\beta = c^E_{1,2}/c^F_{2,1}$, $\epsilon_0 = \kappa^E_{0,1}E_{\mathrm{tot}}$, $\epsilon_1 = (\kappa^E_{1,0}+\kappa^E_{1,2})E_{\mathrm{tot}}$, $\epsilon_2 = \kappa^E_{2,1}E_{\mathrm{tot}}$, $\phi_0 = \kappa^F_{0,1}F_{\mathrm{tot}}$, $\phi_1 = (\kappa^F_{1,0}+\kappa^F_{1,2})F_{\mathrm{tot}}$, $\phi_2 = \kappa^F_{2,1}F_{\mathrm{tot}}$, together with the totals $\sigma = S_{\mathrm{tot}}/E_{\mathrm{tot}}$, $\lambda = S_{\mathrm{tot}}/F_{\mathrm{tot}}$, $\zeta = E_{\mathrm{tot}}/F_{\mathrm{tot}}$ and the free-enzyme fractions $u = [E]/E_{\mathrm{tot}}$, $v = [F]/F_{\mathrm{tot}}$. Then:

1. Zero net flux around each modification loop gives $[S_1] = \alpha([E]/[F])[S_0]$ and $[S_2] = \beta([E]/[F])[S_1]$.
2. Substrate conservation then expresses $[S_0],[S_1],[S_2]$ as rational functions of $[E],[F]$.
3. Conservation of $E$ and $F$ yields two equations $\Phi_1(u,v) = 0$, $\Phi_2(u,v) = 0$, where $\Phi_1, \Phi_2$ are polynomials of total degree 4 in $(u,v)$ whose coefficients depend only on the eight non-dimensional parameters $\alpha, \beta, \epsilon_0, \epsilon_1, \epsilon_2, \phi_0, \phi_1, \phi_2$ and the three totals. Every other steady-state concentration is a rational function of the solution $(u,v)$.

The parameters $\epsilon_0, \epsilon_1, \phi_1, \phi_2$ are always positive, while $\epsilon_2 = 0$ (resp. $\phi_0 = 0$) exactly when $S_1 \xrightarrow{E} S_2$ (resp. $S_1 \xrightarrow{F} S_0$) is strongly irreversible, i.e. forbids product rebinding. Positive solutions $(u,v) \in (0,1)^2$ are the biologically meaningful steady states; one positive solution is monostability and three is bistability.

## Expansion

The key fact is that, in the linear framework, any enzyme mechanism's intermediate complexes at steady state are linear in the free enzyme concentration times free substrate concentrations, with positive coefficients that are rational functions of the rate constants (matrix-tree formulas). This is an instance of the general result that a modification system with $k$ enzymes acting on one substrate has all steady-state concentrations rational in the $k$ free enzyme concentrations, which solve $k$ polynomial equations. Here $k = 2$, and only the aggregate binding of the intermediate modform $S_1$ to each enzyme matters, cutting twelve generalized parameters to ten and then, after nondimensionalization, to eight. Under strong irreversibility of the $S_1$-consuming reactions the system still has degree 4, so Bézout's theorem gives 16 projective solutions; numerically the origin has multiplicity 6 and either one or three of the five remaining finite nonzero solutions are positive. Using homotopy continuation over about $10^9$ sampled parameter points, the bistable region was found to be empty for $\sigma$ below a threshold near $1$ and to grow sigmoidally with $\sigma$.

## Sources

- K.-M. Nam, B. M. Gyori, S. V. Amethyst, D. J. Bates, J. Gunawardena, "Robustness and parameter geography in post-translational modification systems", PLoS Computational Biology 16(5) (2020) e1007573, Results ("Steady-state polynomial equations", Eqs 2–10; "The strongly irreversible case") and Materials and methods ("Derivation of Eq 10"), <https://doi.org/10.1371/journal.pcbi.1007573>, PMCID PMC7224580.
