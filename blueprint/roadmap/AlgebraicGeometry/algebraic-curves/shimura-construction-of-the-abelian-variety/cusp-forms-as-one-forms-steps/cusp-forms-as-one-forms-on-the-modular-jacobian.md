# Weight-two cusp forms as holomorphic $1$-forms on the modular Jacobian

Let $N$ be a positive integer and $\Gamma$ a group of level $N$, that is,
$\Gamma_1(N) \subset \Gamma \subset \Gamma_0(N)$, let $\mathfrak{H}^* = \mathfrak{H} \cup \mathbb{Q} \cup \{\infty\}$, and let $J$ be the
[Jacobian](../../jacobians-of-compact-riemann-surfaces/jacobian.md) of the compact Riemann surface $\mathfrak{H}^*/\Gamma$, a complex abelian variety, with
$D_J$ its space of [holomorphic $1$-forms](../holomorphic-one-forms-steps/holomorphic-one-forms-and-tangent-space.md). Let
$\psi \colon \mathfrak{H}^* \to J$ be the composite of the natural map $\mathfrak{H}^* \to \mathfrak{H}^*/\Gamma$ with an
[Abel–Jacobi map](../../jacobians-of-compact-riemann-surfaces/of-curve.md) $\mathfrak{H}^*/\Gamma \to J$, and let $S_2(\Gamma)$ be the space of weight-two
[cusp forms](../../../../NumberTheory/modular-forms-q-series/modular-forms/cusp-form.md) for $\Gamma$.

There is an isomorphism $\mu \colon S_2(\Gamma) \to D_J$ of complex vector spaces determined by

$$\delta\psi(\mu(f)) = f(z)\,dz \qquad (f \in S_2(\Gamma)),$$

where $\delta\psi$ is the pullback of holomorphic $1$-forms along $\psi$ on $\mathfrak{H}$ and $z$ is the standard
coordinate on $\mathfrak{H}$.

## Depends on

- [Modular curve of a group of level $N$ and its standard model over $\mathbb{Q}$](../../../../NumberTheory/modular-forms-q-series/modular-forms/modular-curve-of-a-group-of-level-n.md), for the compact Riemann surface $\mathfrak{H}^*/\Gamma$ and the Jacobian $J$ of $X_\Gamma$
- [Jacobian of a compact Riemann surface](../../jacobians-of-compact-riemann-surfaces/jacobian.md), for $J$
- [Abel–Jacobi map](../../jacobians-of-compact-riemann-surfaces/of-curve.md), for $\psi$
- [The Abel–Jacobi map is holomorphic](../../jacobians-of-compact-riemann-surfaces/of-curve-cont-mdiff.md), for the
  pullback $\delta\psi$ of holomorphic $1$-forms along $\psi$
- [Holomorphic $1$-forms and tangent space of a complex abelian variety](../holomorphic-one-forms-steps/holomorphic-one-forms-and-tangent-space.md), for $D_J$
- [Cusp form](../../../../NumberTheory/modular-forms-q-series/modular-forms/cusp-form.md), for $S_2(\Gamma)$
- [Congruence subgroup $\Gamma_0(N)$](../../../../NumberTheory/modular-forms-q-series/modular-forms/congruence-subgroup-gamma0.md)
- [Congruence subgroup $\Gamma_1(N)$](../../../../NumberTheory/modular-forms-q-series/modular-forms/congruence-subgroup-gamma1.md)

## Proof depends on

- [Weight-two cusp forms as holomorphic differentials on $\mathfrak{H}^*/\Gamma$](weight-two-cusp-forms-as-holomorphic-differentials.md),
  for the isomorphism $f \mapsto \omega_f$ of $S_2(\Gamma)$ onto the holomorphic differentials on $\mathfrak{H}^*/\Gamma$
- [The Jacobian of a compact Riemann surface and the Jacobian variety of a curve](analytic-jacobian-and-the-jacobian-variety.md),
  for the identification of the Jacobian of $\mathfrak{H}^*/\Gamma$ with $J(\mathbb{C})$, through which it is a complex abelian variety
- [Pullback of holomorphic $1$-forms along an Abel–Jacobi map](pullback-of-one-forms-along-the-abel-jacobi-map.md),
  for the isomorphism of $D_J$ onto the holomorphic differentials on $\mathfrak{H}^*/\Gamma$, independent of the base point
- [Abel–Jacobi map](../../jacobians-of-compact-riemann-surfaces/of-curve.md), for the map along which $D_J$ is pulled back

## Proof sketch

Let $\varphi \colon \mathfrak{H}^*/\Gamma \to J$ be the Abel–Jacobi map through which $\psi$ is defined and
$p \colon \mathfrak{H} \to \mathfrak{H}^*/\Gamma$ the quotient map, so that on $\mathfrak{H}$ the pullback $\delta\psi$ is
$p^* \circ \varphi^*$. Put $\mu(f) = (\varphi^*)^{-1}(\omega_f)$, with $\omega_f$ the holomorphic differential on
$\mathfrak{H}^*/\Gamma$ whose pullback to $\mathfrak{H}$ is $f(z)\,dz$. Then $\delta\psi(\mu(f)) = p^* \omega_f = f(z)\,dz$, and
$\mu$ is an isomorphism as a composite of two isomorphisms. It is determined by this relation, as $\varphi^*$ is
injective and $p^*$ is injective on holomorphic differentials, and it does not depend on the base point of $\varphi$.

## Sources

- G. Shimura, *On the factors of the jacobian variety of a modular function field*, J. Math. Soc.
  Japan 25 (1973), 523–544, <https://doi.org/10.2969/jmsj/02530523>: §1, p. 525 (the map $\psi$ and the isomorphism $\mu$ defined by $\delta\psi(\mu(f)) = f(z)\,dz$).
