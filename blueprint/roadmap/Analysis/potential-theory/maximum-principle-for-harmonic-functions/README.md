# Maximum principle for harmonic functions

The maximum principle is the first structural property of harmonic functions in the classical
theory of Laplace's equation, and the reason solutions of the Dirichlet problem are unique. On a nonempty bounded open
set $U \subseteq \mathbb{R}^n$ with $n \ge 1$, a function $u \in C^2(U) \cap C(\overline U)$ with
$\Delta u \ge 0$ attains its maximum over $\overline U$ on $\partial U$ (weak maximum principle);
for harmonic $u$ the same holds for the minimum, so two solutions of $-\Delta u = f$ with the same
boundary values coincide. On a connected $U$, an interior maximum forces a harmonic function to be
constant (strong maximum principle), a consequence of the mean-value property: a $C^2$ function is
harmonic exactly when its average over every ball $\overline{B}(x, r) \subseteq U$ equals $u(x)$.

The pages below give the weak maximum and minimum principles and uniqueness for the Dirichlet problem
on nonempty bounded open sets of any finite-dimensional real inner product space of positive dimension, by the perturbation argument: $u + \varepsilon |x|^2$ has
positive Laplacian, while the Laplacian of a $C^2$ function is nonpositive at an interior maximum.
In the plane they give the strong maximum principle too, by writing a harmonic function locally as
the real part of a holomorphic one and applying the maximum modulus principle. The
mean-value property in dimension $n$, Harnack's inequality and the strong maximum principle in
every dimension are stated as well.

- [Second derivative along a line](iterated-fderiv-two-apply-eq-deriv-deriv.md)
- [Nonpositive second derivatives at a local maximum](iterated-fderiv-two-nonpos-of-is-local-m.md)
- [The Laplacian is nonpositive at an interior maximum](laplacian-nonpos-of-is-local-max.md)
- [Laplacian of the squared norm](laplacian-norm-sq.md)
- [Weak maximum principle for subharmonic functions](exists-mem-frontier-is-max-on-of-laplaci.md)
- [Weak maximum principle for harmonic functions](exists-mem-frontier-is-max-on-of-harmoni.md)
- [Weak minimum principle for harmonic functions](exists-mem-frontier-is-min-on-of-harmoni.md)
- [Uniqueness for the Dirichlet problem for Poisson's equation](eq-on-closure-of-neg-laplacian-eq.md)
- [Mean-value property of harmonic functions, and its converse](harmonic-on-nhd-iff-forall-average-close.md)
- [Strong maximum principle for harmonic functions](eq-on-closure-of-is-max-on-harmonic-on-n.md)
- [A planar harmonic function is constant near an interior maximum](exists-ball-eq-on-of-is-max-on-complex.md)
- [Strong maximum principle for planar harmonic functions](eq-on-of-is-max-on-complex.md)
- [Harnack's inequality for harmonic functions](harnack-inequality.md)

## Related topics

- [Subharmonic functions](../subharmonic-functions/README.md): subharmonicity through the
  sub-mean-value property, the setting in which the maximum principle extends beyond $C^2$.
- [Fundamental solutions of the Laplacian](../fundamental-solutions-of-the-laplacian/README.md):
  the explicit harmonic functions behind Green's representation and the mean-value formulas.
- [Heat equation](../../partial-differential-equations/heat-equation/README.md): the parabolic
  maximum principle on space-time cylinders, proved by the same perturbation argument.
- [Weak solutions of elliptic equations](../../partial-differential-equations/weak-solutions-of-elliptic-equations/README.md):
  existence for the Dirichlet problem in $H^1_0(U)$, complementing the uniqueness of classical
  solutions above.
- [Viscosity solutions of Hamilton–Jacobi equations](../../partial-differential-equations/viscosity-solutions-of-hamilton-jacobi-equations/README.md):
  comparison principles for nonlinear equations, which extend the maximum-principle argument
  (touching from above at a maximum) to merely continuous solutions.
