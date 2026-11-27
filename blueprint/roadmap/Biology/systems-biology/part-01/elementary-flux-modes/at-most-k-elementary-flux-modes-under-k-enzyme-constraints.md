# At most K elementary flux modes under K enzyme constraints

**Kinetic model.** Let $N \in \mathbb{R}^{m \times r}$ be a stoichiometric matrix with all reactions
irreversible (reversible ones split), so steady-state fluxes form the cone
$P = \{ v \in \mathbb{R}^r : N v = 0,\ v \ge 0 \}$. Each reaction $j$ is catalysed by an enzyme of
concentration $e_j \ge 0$ with rate

$$v_j = e_j\, k_{\mathrm{cat},j}\, f_j(x),$$

where $k_{\mathrm{cat},j} > 0$ and $f_j(x) > 0$ is an arbitrary (nonlinear) saturation function of the
metabolite concentrations $x = (x_E, x_I)$; external concentrations $x_E$ are fixed and internal ones
$x_I$ are free. Enzyme levels obey $K$ linear pool constraints with weights $w^{(k)}_j \ge 0$:

$$C^{(k)}_{\Sigma} := \sum_{j=1}^{r} w^{(k)}_j e_j \le 1, \qquad k = 1, \dots, K .$$

**Cost vectors.** Scale each elementary flux mode (EFM) carrying the objective flux $v_r$ so that
$\mathrm{EFM}_i = (V^i_1, \dots, V^i_{r-1}, 1)^{T}$. Its cost vector $d^i(x) \in \mathbb{R}^K$ has entries

$$d^i_k(x) = \sum_{j=1}^{r} \frac{w^{(k)}_j V^i_j}{k_{\mathrm{cat},j} f_j(x)},$$

the fraction of pool $k$ used per unit of objective flux through $\mathrm{EFM}_i$. Two EFMs are
**equivalent** if their cost vectors coincide.

**Theorem (extremum principle).** Maximize the objective flux $v_r$ over $v \in P$, $x_I$ and $e$
subject to the $K$ constraints. Then an optimum is attained by a flux vector that is a nonnegative
combination of at most $K$ non-equivalent EFMs; more EFMs can carry flux at an optimum only by
substituting EFMs with identical cost vectors.

**Corollary.** If an optimized flux uses $K$ non-equivalent EFMs, at least $K$ enzyme constraints
are active.

## Depends on

- [Elementary modes are the extreme rays of the split flux cone](elementary-modes-are-extreme-rays-of-the-split-flux-cone.md)

## Expansion

Writing $v = \sum_{i=1}^{M} \lambda_i \mathrm{EFM}_i$ with $\lambda_i \ge 0$ (possible because EFMs
generate the pointed cone) gives $v_r = \sum_i \lambda_i$ and, using $e_j = v_j / (k_{\mathrm{cat},j}
f_j(x))$, $C^{(k)}_{\Sigma} = \sum_i \lambda_i d^i_k(x)$. For fixed internal concentrations the problem
becomes the linear program

$$\max_{\lambda \ge 0}\ \mathbf{1}^{T}\lambda \quad \text{subject to} \quad D(x)\,\lambda \le \mathbf{1},
\qquad D(x) = [\, d^1(x) \cdots d^M(x) \,] \in \mathbb{R}^{K \times M}.$$

An optimum is attained at a vertex of the feasible polytope, where at least $M$ of the $M + K$
constraints are tight, so at most $K$ of the $\lambda_i$ are positive. This holds for every $x$, hence
also at the optimal internal concentrations, independently of network size, topology or kinetics.
With a single constraint ($K = 1$, e.g. total protein) it recovers the earlier result that maximal
specific flux is attained in a single EFM; with two constraints it explains the switch from pure
respiration to respiration plus overflow metabolism at a critical growth rate.

## Sources

- D. H. de Groot, C. van Boxtel, R. Planqué, F. J. Bruggeman, B. Teusink, "The number of active
  metabolic pathways is bounded by the number of cellular constraints at maximal metabolic rates",
  PLoS Computational Biology 15 (2019) e1006858, Eqs. (1)-(9), Definition 1, Theorem 1 and
  Corollary 2, <https://doi.org/10.1371/journal.pcbi.1006858> (PMC6428345).
- M. T. Wortel, H. Peters, J. Hulshof, B. Teusink, F. J. Bruggeman, "Metabolic states with maximal
  specific rate carry flux through an elementary flux mode", FEBS Journal 281 (2014) 1547-1555,
  <https://doi.org/10.1111/febs.12722>.
