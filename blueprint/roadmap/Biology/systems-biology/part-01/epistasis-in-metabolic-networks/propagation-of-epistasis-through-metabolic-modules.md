# Propagation of epistasis through metabolic modules

**Modules and effective rates.** Consider a metabolic network of first-order reversible reactions
$i \leftrightarrow j$ with rate constants $x_{ij}$. A **module** $\mu$ is a set of internal metabolites
that exchange material with the rest of the network only through two input/output (I/O) metabolites.
At quasi-steady state the module can be replaced by a single first-order reaction between its I/O
metabolites with effective rate constant

$$y_\mu = F(\vec x_\mu),$$

which depends only on the module's own rate matrix $\vec x_\mu$; the replacement leaves the dynamics
of all external metabolites unchanged (the biochemical analogue of the star–mesh transformation, or
Kron reduction). If $\mu$ is nested in a larger module $\nu$, then $y_\nu$ depends on $\vec x_\mu$ only
through $y_\mu$:

$$y_\nu = f_1(y_\mu),$$

with the remaining rate constants of $\nu$ as parameters.

**Epistasis coefficient.** For mutations $A$, $B$ with relative effects $\delta_A y$, $\delta_B y$
and joint effect $\delta_{AB} y$ on a phenotype $y$, define

$$\varepsilon y = \frac{\delta_{AB} y - \delta_A y - \delta_B y}{2\, \delta_A y\, \delta_B y}.$$

**Propagation law.** If the mutational effects at level $\mu$ are small,

$$\varepsilon y_\nu = \frac{\varepsilon y_\mu}{C} + \frac{H}{2C^2} + o(1), \qquad
C = \frac{f_1'(y_\mu)\, y_\mu}{y_\nu}, \quad H = \frac{f_1''(y_\mu)\, y_\mu^2}{y_\nu},$$

where $C$ and $H$ are the first- and second-order control coefficients of module $\mu$ over the flux
of $\nu$. This is an affine map with slope $1/C$ and fixed point
$\bar\varepsilon = -H\,\bigl(2C(1 - C)\bigr)^{-1}$.

**Theorem.** For every module $\nu$ containing $\mu$,

$$0 \le C \le 1 \qquad\text{and}\qquad 0 \le \bar\varepsilon \le 1 .$$

Consequently, in the small-effect limit, negative epistasis propagates to negative epistasis of
at least the same magnitude ($\varepsilon y_\nu \le \varepsilon y_\mu < 0$), strong positive epistasis
to stronger positive epistasis ($\varepsilon y_\nu \ge \varepsilon y_\mu > 1$), and only weak positive
epistasis ($0 < \varepsilon y_\mu < 1$) can change regime, regardless of topology or rate constants.

## Depends on

- [Flux control coefficient](../../stochastic-mass-action-metabolic-control-and-flu/flux-control.md)

## Expansion

The propagation law is a second-order Taylor expansion of $f_1$ around the wild-type $y_\mu$,
written in relative effects. Its content lies in the bounds. Although there are infinitely many
module topologies, every higher-level module falls into one of three topological classes according
to where the lower-level module sits relative to its own I/O metabolites, and each class gives a
parametric family for $f_1$ whose $C$ and $H$ can be computed explicitly. For a linear pathway, for
example, $C = (1 + \alpha y_\mu)^{-1}$ and $H = -2\alpha y_\mu (1 + \alpha y_\mu)^{-2}$ with $\alpha > 0$:
$f_1$ is increasing and concave, because other steps become limiting. Since the slope $1/C \ge 1$,
the fixed point $\bar\varepsilon \in [0, 1]$ is unstable, which yields the three regimes. The main
qualitative prediction is that negative epistasis in a lower-level phenotype can never become
positive epistasis at a higher level, whereas the converse is possible.

## Sources

- S. Kryazhimskiy, "Emergence and propagation of epistasis in metabolic networks", eLife 10 (2021)
  e60200, Eqs. (1)-(8) and Theorem 1, <https://doi.org/10.7554/eLife.60200> (PMC7924954).
