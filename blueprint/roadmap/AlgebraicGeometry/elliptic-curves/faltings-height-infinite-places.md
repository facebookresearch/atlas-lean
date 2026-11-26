# The infinite places in Silverman's formula for the Faltings height

Let $L$ be a number field, let $E$ be an elliptic curve over $L$, let $\omega$ and the metrics
$\| \cdot \|_\sigma$ be those of the
[Faltings height of $E/L$](faltings-height-over-the-field-of-definition.md), extended to
$\omega^{\otimes 12}$ by $\| s^{\otimes 12} \|_\sigma = \| s \|_\sigma^{12}$, and let
$\beta_E = \Delta_W \, \omega_W^{\otimes 12}$ be the element of
$H^0(E, \Omega^1_{E/L})^{\otimes 12}$ given by any Weierstrass equation $W$ of $E$ over $L$, which does
not depend on $W$ ([the invariant differential of a Weierstrass equation](invariant-differential-of-a-weierstrass-equation.md)).
Fix an embedding $\sigma : L \to \mathbb{C}$, let $\beta_\sigma$ be the image of $\beta_E$ in
$H^0(E_\sigma, \Omega^1)^{\otimes 12}$, and, by the
[complex uniformization](complex-uniformization.md), choose $\tau \in \mathbb{H}$ and an isomorphism
of $E_\sigma$ with the curve $Y^2 = 4X^3 - g_2(\tau) X - g_3(\tau)$; identify $E_\sigma(\mathbb{C})$
with $\mathbb{C}/(\mathbb{Z} + \mathbb{Z}\tau)$ through it and $z \mapsto (\wp(z), \wp'(z))$. Let
$\Delta(\tau) = g_2(\tau)^3 - 27 g_3(\tau)^2$ as in
[Jacobi's product formula](../../NumberTheory/modular-forms-q-series/modular-forms/lattice-discriminant-eta-product.md).

**Theorem.** On $\mathbb{C}/(\mathbb{Z} + \mathbb{Z}\tau)$, $\beta_\sigma = \Delta(\tau) \, (dz)^{\otimes 12}$.
For every $\alpha \in H^0(E_\sigma, \Omega^1)$ with $\alpha^{\otimes 12} = \beta_\sigma$, such as
$\alpha = \Delta(\tau)^{1/12} dz$ for any twelfth root,

$$\frac{i}{2} \int_{\mathbb{C}/(\mathbb{Z} + \mathbb{Z}\tau)} \alpha \wedge \bar\alpha = |\Delta(\tau)|^{1/6} \operatorname{Im} \tau ,$$

and so

$$\log \| \beta_E \|_\sigma = 6 \log \Bigl( \frac{i}{2} \int \alpha \wedge \bar\alpha \Bigr)
  = \log \bigl( |\Delta(\tau)| \, (\operatorname{Im} \tau)^6 \bigr).$$

*Proof* (Silverman, pp. 255–256). With $X = x$ and $Y = 2y$, the curve
$Y^2 = 4X^3 - g_2 X - g_3$ has the Weierstrass equation
$y^2 = x^3 - \frac{g_2}{4} x - \frac{g_3}{4}$, with discriminant $g_2^3 - 27 g_3^2 = \Delta(\tau)$ and
invariant differential $dx / 2y = dX / Y$. Since $\beta$ does not depend on the Weierstrass equation,
$\beta_\sigma = \Delta(\tau) (dX/Y)^{\otimes 12}$, and $dX/Y$ pulls back to $dz$, so
$\beta_\sigma = \Delta(\tau) (dz)^{\otimes 12}$. Then $\alpha = c \, dz$ with $|c| = |\Delta(\tau)|^{1/12}$,
and since $dz \wedge d\bar z = -2i \, dx \wedge dy$,
$\frac{i}{2} \int \alpha \wedge \bar\alpha = |\Delta(\tau)|^{1/6} \int dx \wedge dy$, the integral
being over a fundamental parallelogram of $\mathbb{Z} + \mathbb{Z}\tau$, whose area is
$\operatorname{Im} \tau$. Finally $\| \beta_E \|_\sigma = \| \alpha \|_\sigma^{12}$ and
$\| \alpha \|_\sigma^2 = \frac{i}{2} \int \alpha \wedge \bar\alpha$.

## Depends on

- [Faltings height of an elliptic curve over its field of definition](faltings-height-over-the-field-of-definition.md),
  for the metrics $\| \cdot \|_\sigma$
- [The invariant differential of a Weierstrass equation](invariant-differential-of-a-weierstrass-equation.md),
  for $\beta_E$
- [Complex uniformization of elliptic curves](complex-uniformization.md), for $\tau$, the
  isomorphism and the parametrization by $\wp$
- [Jacobi's product formula for the discriminant of a lattice](../../NumberTheory/modular-forms-q-series/modular-forms/lattice-discriminant-eta-product.md),
  for $g_2(\tau)$, $g_3(\tau)$ and $\Delta(\tau)$

## Proof depends on

- [The invariant differential of a Weierstrass equation](invariant-differential-of-a-weierstrass-equation.md),
  item 3, for the independence of $\beta$ from the Weierstrass equation
- [Complex uniformization of elliptic curves](complex-uniformization.md), item 1, for the pullback of
  $dX/Y$ to $dz$
- [Area of a fundamental parallelogram](../../Analysis/special-functions/elliptic-functions/fundamental-parallelograms-of-complex-lattices/area-of-fundamental-parallelogram.md),
  for the area $\operatorname{Im} \tau$ and the reduction of the integral over
  $\mathbb{C}/(\mathbb{Z} + \mathbb{Z}\tau)$ to one over a fundamental parallelogram

## Sources

- J. H. Silverman, "Heights and elliptic curves", in G. Cornell and J. H. Silverman (eds.),
  *Arithmetic Geometry* (Storrs, 1984), Springer, New York, 1986, 253–265,
  <https://doi.org/10.1007/978-1-4613-8655-1_10>: proof of Proposition 1.1, pp. 255–256, the
  Weierstrass equation (3) with discriminant $\Delta_v = g_2(\tau_v)^3 - 27 g_3(\tau_v)^2 = \Delta(\tau_v)$
  (p. 255), $\beta = \Delta(\tau) (dX_v / Y_v)^{\otimes 12} = \Delta(\tau) (dz)^{\otimes 12}$ on
  $\mathbb{C}/(\mathbb{Z} + \mathbb{Z}\tau)$, $\alpha = \Delta(\tau)^{1/12} dz$, the computation
  $\frac{i}{2} \int \alpha \wedge \bar\alpha = |\Delta(\tau)|^{1/6} \operatorname{Im}(\tau)$ through the
  area of a fundamental parallelogram, and the contribution
  $-(n_v / 12 [K : \mathbb{Q}]) \log(|\Delta(\tau_v)| \operatorname{Im}(\tau_v)^6)$ of $v \in M_K^\infty$
  (p. 256).
