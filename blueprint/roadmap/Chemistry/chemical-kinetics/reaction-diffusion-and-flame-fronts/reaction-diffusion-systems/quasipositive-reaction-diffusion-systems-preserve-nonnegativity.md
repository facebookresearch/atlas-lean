# Quasipositive reaction-diffusion systems preserve nonnegativity

This node covers invariance of the nonnegative cone for reaction-diffusion systems. Let $\Omega \subset \mathbb{R}^d$ be bounded with
smooth boundary, $d_1, \dots, d_m > 0$, and $f : \mathbb{R}^m \to \mathbb{R}^m$ locally Lipschitz and quasipositive: $f_i(c) \ge 0$ whenever
$c \in [0, \infty)^m$ and $c_i = 0$. Let $c$ be a classical solution on $\overline\Omega \times [0, T)$ of
$\partial_t c_i = d_i\,\Delta c_i + f_i(c)$ with homogeneous Neumann boundary conditions and continuous initial data $c(\cdot, 0) \ge 0$.
Then $c_i(x, t) \ge 0$ for all $i$, $x \in \overline\Omega$ and $t \in [0, T)$. If moreover $\sum_i f_i \le 0$ on $[0, \infty)^m$, the total mass
$\sum_i \int_\Omega c_i\,dx$ is nonincreasing.

## Depends on

- [Parabolic boundary maximum principle](../../../../Analysis/partial-differential-equations/heat-equation/exists-mem-parabolic-boundary-is-max-on.md)

## Expansion

A good expansion proves nonnegativity by a comparison argument applied to a modified system whose nonlinearity is extended to
negative values by $f_i(c^+)$, using the scalar parabolic maximum principle for each component and uniqueness of classical solutions. Global
existence for mass-controlled systems, energy coupling and nonisothermal kinetics are separate nodes.

## Sources

- M. Pierre, Global existence in reaction-diffusion systems with control of mass: a survey, *Milan Journal of Mathematics* 78 (2010) 417-455.
