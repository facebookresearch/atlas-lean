# Ou-Yang–Helfrich shape equation and the second variation of a spherical vesicle

For a closed lipid vesicle with bending modulus $k_c > 0$, spontaneous curvature $c_0$, surface tension $\lambda$ and pressure difference $p = p_{\text{out}} - p_{\text{in}}$, take the free energy $F = \frac{k_c}{2}\oint (2H + c_0)^2\, dA + \lambda A + p V$, with mean curvature $H$ and Gaussian curvature $K$ in the convention where a sphere of radius $R$ has $H = -1/R$, $K = 1/R^2$. In the shape equation, $\nabla^2$ is the [Laplace–Beltrami operator](../../../Geometry/riemannian-geometry/laplace-beltrami-operator/laplacian.md) of the surface with its induced metric, in the sign convention $\nabla^2 = \operatorname{div} \circ \operatorname{grad}$, the trace of the covariant Hessian (the source's $(\nabla^2 u)\, dA = d \ast du$), so that $-\nabla^2$ is nonnegative and $\nabla^2 Y_{lm} = -l(l+1)R^{-2}\,Y_{lm}$ on a sphere of radius $R$. Equilibrium shapes satisfy the Ou-Yang–Helfrich shape equation

$$p - 2\lambda H + k_c (2H + c_0)(2H^2 - c_0 H - 2K) + 2 k_c \nabla^2 H = 0$$

(Tu and Ou-Yang, Eq. (77)). At a sphere of radius $R > 0$ that satisfies the [sphere condition](../../not-yet-classified/helfrich-sphere-stability/shape-lhs-sphere-eq-zero-iff.md), the second variation of $F$ along a normal perturbation $\sum_{l, m} a_{lm} Y_{lm}$ (truncated at a finite degree) is the diagonal form $\sum_{l, m} |a_{lm}|^2 q_l(p)$ of the [second variation](../../not-yet-classified/helfrich-sphere-stability/second-variation.md) page, with the [mode coefficients](../../not-yet-classified/helfrich-sphere-stability/mode-coeff.md)

$$q_l(p) = \frac{R}{2}\bigl[l(l+1) - 2\bigr]\Bigl\{\frac{2k_c\bigl[l(l+1) - c_0 R\bigr]}{R^3} - p\Bigr\}$$

(from the source's Eq. (82)); for $l = 0$ this gives $q_0(p) = Rp + 2k_c c_0/R$. The resulting stability thresholds at $p_c = 2k_c(6 - c_0 R)/R^3$ for perturbations with $a_{00} = 0$ are the [semidefinite](../../not-yet-classified/helfrich-sphere-stability/second-variation-nonneg-iff.md) and [strict](../../not-yet-classified/helfrich-sphere-stability/second-variation-pos-iff.md) stability criteria. Without a constraint fixing the volume or the area, the radial mode is not excluded and "stable for $p < p_c$" fails: $k_c = R = 1$, $c_0 = 0$, $p = -1$, $\lambda = 1/2$ is an equilibrium with $p < p_c = 12$ but $F''(R) = -4\pi$ for radial changes.

## Depends on

- [Laplace–Beltrami operator](../../../Geometry/riemannian-geometry/laplace-beltrami-operator/laplacian.md)
- [The sphere condition](../../not-yet-classified/helfrich-sphere-stability/shape-lhs-sphere-eq-zero-iff.md)
- [Second Variation](../../not-yet-classified/helfrich-sphere-stability/second-variation.md)
- [Mode Coeff](../../not-yet-classified/helfrich-sphere-stability/mode-coeff.md)

## Expansion

1. The model: closed smooth surfaces, the free energy with pressure and tension terms, the curvature sign convention, the sign convention of the surface Laplace–Beltrami operator, and the class of admissible normal variations (with or without volume and area constraints).
2. The first variation and the shape equation, as in the source.
3. The second variation of $F$ at an equilibrium sphere in spherical harmonics: its identification with the diagonal form with coefficients $q_l$ for $l \ge 1$ and the radial coefficient $q_0$.
4. The radial counterexample without volume or area constraints.

## Sources

- Z.-C. Tu and Z.-C. Ou-Yang, Elastic theory of low-dimensional continua and its applications in bio- and nano-structures, J. Comput. Theor. Nanosci. 5 (2008), 422–448, Eqs. (77), (82) and the appendix on differential forms. <https://arxiv.org/abs/0706.0001>
- Original result: Z.-C. Ou-Yang and W. Helfrich, Instability and deformation of a spherical vesicle by pressure, Phys. Rev. Lett. 59 (1987), 2486–2488. <https://doi.org/10.1103/PhysRevLett.59.2486> The equations follow Tu and Ou-Yang (2008).
- Original result: Z.-C. Ou-Yang and W. Helfrich, Bending energy of vesicle membranes: general expressions for the first, second, and third variation of the shape energy and applications to spheres and cylinders, Phys. Rev. A 39 (1989), 5280–5288. <https://doi.org/10.1103/PhysRevA.39.5280> The equations follow Tu and Ou-Yang (2008).
