# Ou-Yang–Helfrich shape equation and the stability of spherical vesicles

For a closed lipid vesicle with bending modulus $k_c > 0$, spontaneous curvature $c_0$, surface tension $\lambda$ and pressure difference $p = p_{\text{out}} - p_{\text{in}}$, take the free energy $F = \frac{k_c}{2}\oint (2H + c_0)^2\, dA + \lambda A + p V$, with mean curvature $H$ and Gaussian curvature $K$ in the convention where a sphere of radius $R$ has $H = -1/R$, $K = 1/R^2$. Equilibrium shapes satisfy the Ou-Yang–Helfrich shape equation
$$p - 2\lambda H + k_c (2H + c_0)(2H^2 - c_0 H - 2K) + 2 k_c \nabla^2 H = 0,$$
and a sphere of radius $R > 0$ is an equilibrium exactly when $pR^2 + 2\lambda R - k_c c_0(2 - c_0 R) = 0$ (Tu and Ou-Yang, Eqs. (77), (78)). For a normal perturbation expanded in spherical harmonics $Y_{lm}$, the second variation at such a sphere has, for $l \ge 1$, the coefficient
$$\frac{R}{2}\bigl[l(l+1) - 2\bigr]\Bigl\{\frac{2k_c\bigl[l(l+1) - c_0 R\bigr]}{R^3} - p\Bigr\}$$
(from the source's Eq. (82)): it vanishes for $l = 1$ (translations), is positive for every $l \ge 2$ when $p < p_c = 2k_c(6 - c_0 R)/R^3$ (Eq. (83)), vanishes for $l = 2$ at $p = p_c$, and is negative for $l = 2$ when $p > p_c$. The radial mode $l = 0$ has the separate coefficient $Rp + 2k_c c_0/R$; the statement "stable for $p < p_c$" refers to perturbations without an $l = 0$ component, for example under constraints fixing the volume or the area, and fails otherwise ($k_c = R = 1$, $c_0 = 0$, $p = -1$, $\lambda = 1/2$ is an equilibrium with $p < p_c = 12$ but $F''(R) = -4\pi$ for radial changes).

## Expansion

1. The model: closed smooth surfaces, the free energy with pressure and tension terms, the curvature sign convention, and the class of admissible normal variations (with or without volume and area constraints).
2. The first variation and the shape equation, as in the source.
3. The sphere solution and its radius condition.
4. The second variation of a sphere in spherical harmonics: the coefficients for $l \ge 1$, the radial coefficient for $l = 0$, the threshold $p_c$, the translation zero modes and the $l = 2$ equality at $p_c$, each as a separate statement.

## Sources

- Z.-C. Tu and Z.-C. Ou-Yang, Elastic theory of low-dimensional continua and its applications in bio- and nano-structures, J. Comput. Theor. Nanosci. 5 (2008), 422–448, Eqs. (77), (78), (82), (83). <https://arxiv.org/abs/0706.0001>
- Original result: Z.-C. Ou-Yang and W. Helfrich, Instability and deformation of a spherical vesicle by pressure, Phys. Rev. Lett. 59 (1987), 2486–2488. <https://doi.org/10.1103/PhysRevLett.59.2486> The equations follow Tu and Ou-Yang (2008).
- Original result: Z.-C. Ou-Yang and W. Helfrich, Bending energy of vesicle membranes: general expressions for the first, second, and third variation of the shape energy and applications to spheres and cylinders, Phys. Rev. A 39 (1989), 5280–5288. <https://doi.org/10.1103/PhysRevA.39.5280> The equations follow Tu and Ou-Yang (2008).
