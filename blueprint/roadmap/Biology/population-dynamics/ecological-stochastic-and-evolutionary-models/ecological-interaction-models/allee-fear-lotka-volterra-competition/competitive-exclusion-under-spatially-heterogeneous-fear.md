# Competitive exclusion under spatially heterogeneous fear in the Allee competition model

**Model.** On a bounded domain $\Omega \subset \mathbb{R}^n$ with Neumann boundary conditions, consider the reaction–diffusion version of the Allee–fear Lotka–Volterra competition system

$$u_t = d_1 \Delta u + u\Big[(1-u)(u-p)\frac{1}{1+q(x)v} - a v\Big],\qquad v_t = d_2 \Delta v + b\,v\,(1 - v - c u),$$

with $0 < p < 1$, $a, b, c > 0$, flat positive initial data, and a fear function $q \in C^1(\Omega)$, $q \ge 0$, vanishing at most on a set of measure zero. Write $\hat{q} = \min_\Omega q$ and $\tilde{q} = \max_\Omega q$, and for a constant $\mathbf{q}$ let $A_1 = ac^2\mathbf{q} + 1$, $A_2 = -(2ac\mathbf{q} + ac + p + 1)$, $A_3 = a + a\mathbf{q} + p$ and $\Delta(\mathbf{q}) = A_2^2 - 4A_1A_3$.

**Comparison principle.** Let $\bar{u}$, $\hat{u}$, $\widetilde{u}$ and $\underline{u}$ be the first components of the same system with fear term replaced by $1$, $1/(1+\hat{q}\hat{v})$, $1/(1+\tilde{q}\widetilde{v})$ and $1/(1+\tilde{q})$ respectively. Then pointwise

$$\underline{u} \le \widetilde{u} \le u \le \hat{u} \le \bar{u}.$$

**Exclusion of the fearful species.** If

$$\big(2ac\mathbf{q} + ac + p + 1\big)^2 < 4\big(ac^2\mathbf{q} + 1\big)\big(a + a\mathbf{q} + p\big)\qquad\text{for both } \mathbf{q} = \hat{q} \text{ and } \mathbf{q} = \tilde{q},$$

i.e. $\Delta(\hat{q}) < 0$ and $\Delta(\tilde{q}) < 0$, then the solution converges uniformly to the competitor-only state $(0,1)$ as $t \to \infty$, for flat initial data and, more generally, for any initial data in $L^\infty(\Omega)$.

**Bistable exclusion.** If $\Delta > 0$, $2A_1 + A_2 > 0$, $1 \le c \le 1/\mathbf{q} + 1$ and $0 < p < 1/c$ for both $\mathbf{q} = \hat{q}, \tilde{q}$, then there exist initial data (chosen in a wedge at the interior saddle $E_{1*}$, below both separatrices of the bounding constant-fear systems) whose solutions converge uniformly to $(1,0)$, and there exist initial data whose solutions converge uniformly to $(0,1)$. This is not a statement about all small data: if $\sup u_0 < p$, comparison gives $u \to 0$.

**No Turing patterns for constant fear.** If $q(x) \equiv q > 0$ is constant, the system has no diffusion-driven instability for any parameters or diffusion coefficients $d_1, d_2$.

## Depends on

- [Linearly unstable Fourier mode](../../../../pattern-formation/turing-patterns-and-diffusion-driven-instability/is-unstable-mode.md)
- [Equilibria and bifurcations of the Lotka–Volterra competition model with Allee and fear effects](equilibria-and-bifurcations-of-the-allee-fear-competition-model.md)

## Proof depends on

- [Mode instability iff the dispersion polynomial is negative](../../../../pattern-formation/turing-patterns-and-diffusion-driven-instability/is-unstable-mode-iff-dispersion-det-neg.md)

## Expansion

Since $v \le 1$ by comparison with the logistic equation, the fear factor satisfies $1/(1+\tilde{q}) \le 1/(1+q(x)v) \le 1/(1+\hat{q}v) \le 1$, and the comparison principle for the cooperative-in-$u$ ordering gives the sandwich. With $\Delta < 0$ at both extreme fear levels the constant-fear kinetics have no interior equilibrium, so the bounding systems drive $u$ to $0$ and squeeze the true solution to $(0,1)$. In the bistable case both bounding kinetic systems have an interior saddle whose stable manifold separates the basins of $(1,0)$ and $(0,1)$; choosing data inside a wedge where the two separatrices are ordered gives the stated dichotomy. For constant fear the linearization at an interior equilibrium has $B_2, B_3, B_4 < 0$ and positive determinant, which forces $B_1 < 0$ and violates the necessary Turing condition. Heterogeneous fear can therefore decide the competitive outcome only through its extreme values in these sufficient conditions.

## Sources

- Shangming Chen, Fengde Chen, Vaibhava Srivastava and Rana D. Parshad, "Dynamical analysis of a Lotka–Volterra competition model with both Allee and fear effects", International Journal of Biomathematics 17 (2023), 2350077, <https://doi.org/10.1142/s1793524523500778>; numbering as in arXiv:2303.04919: Theorems 6.7, 6.8, 6.10 and 6.13 and Corollary 6.9.
