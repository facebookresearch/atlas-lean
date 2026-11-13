# Generating function of ten classical statistics over a pair of patterns

For
permutations $\tau$ and $\rho$ of $\{0, 1, 2\}$, let $S_n(\tau, \rho)$ be the set of permutations
of $\{0, 1, \dots, n-1\}$ that contain neither $\tau$ nor $\rho$ as a classical pattern. The
generating function $F_{(\tau, \rho)}$ is the formal power series

$$F_{(\tau, \rho)} = \sum_{n \ge 0} \sum_{\sigma \in S_n(\tau, \rho)} x^n
p^{\mathrm{asc}(\sigma)} q^{\mathrm{des}(\sigma)} u^{\mathrm{lrmax}(\sigma)}
v^{\mathrm{rlmax}(\sigma)} s^{\mathrm{lrmin}(\sigma)} t^{\mathrm{rlmin}(\sigma)}
y^{\mathrm{dasc}(\sigma)} z^{\mathrm{ddes}(\sigma)} \ell^{\mathrm{pk}(\sigma)}
m^{\mathrm{vl}(\sigma)}$$

in $x$ with coefficients in the polynomial ring $\mathbb{Q}[p, q, u, v, s, t, y, z, \ell, m]$.
Here $\mathrm{asc}$ and $\mathrm{des}$ count ascents and descents, $\mathrm{lrmax}$ and
$\mathrm{rlmax}$ left-to-right and right-to-left maxima, $\mathrm{lrmin}$ and $\mathrm{rlmin}$
left-to-right and right-to-left minima, $\mathrm{dasc}$ and $\mathrm{ddes}$ double ascents and
double descents, and $\mathrm{pk}$ and $\mathrm{vl}$ peaks and valleys. The empty permutation
($n = 0$) contributes the constant term $1$.

## Sources

- Han, *Joint Distributions of 10 Classical Statistics over Permutations Avoiding Two Patterns of Length 3*, INTEGERS 26 (2026), Article A18, Section 1 (the g.f. `F_(τ,ρ)`).
