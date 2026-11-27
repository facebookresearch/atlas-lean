# Pullback of holomorphic $1$-forms along an Abel–Jacobi map

Let $X$ be a compact Riemann surface with
[Jacobian](../../jacobians-of-compact-riemann-surfaces/jacobian.md) $J(X)$, let $D_{J(X)}$ be the
complex vector space of holomorphic $1$-forms on $J(X)$ and $\Omega^1(X)$ that of holomorphic differentials on $X$, and
for $P \in X$ let $\varphi_P \colon X \to J(X)$ be the
[Abel–Jacobi map](../../jacobians-of-compact-riemann-surfaces/of-curve.md) based at $P$. Then the
pullback of holomorphic $1$-forms

$$\varphi_P^* \colon D_{J(X)} \to \Omega^1(X)$$

is an isomorphism of complex vector spaces, and it does not depend on $P$.

In the classical model $J(X) = \Omega^1(X)^\vee / H_1(X, \mathbb{Z})$, with $\varphi_P(Q)$ the class of
$\omega \mapsto \int_P^Q \omega$, the inverse sends $\omega \in \Omega^1(X)$ to the translation-invariant $1$-form on
$J(X)$ whose value at the origin is the linear form $\lambda \mapsto \lambda(\omega)$ on $\Omega^1(X)^\vee$.

## Depends on

- [Jacobian of a compact Riemann surface](../../jacobians-of-compact-riemann-surfaces/jacobian.md),
  for $J(X)$
- [Abel–Jacobi map](../../jacobians-of-compact-riemann-surfaces/of-curve.md), for $\varphi_P$

## Proof depends on

- [Abel–Jacobi map](../../jacobians-of-compact-riemann-surfaces/of-curve.md), for the maps
  $\varphi_P$ and $\varphi_{P'}$, which differ by a translation of $J(X)$

## Expansion

This node is still to be broken down. A good expansion states and links:

- the classical model of $J(X)$ by periods, the embedding of $H_1(X, \mathbb{Z})$ as a lattice in $\Omega^1(X)^\vee$,
  and $\varphi_P$ by integration;
- the computation of $\varphi_P^*$ on the translation-invariant $1$-forms: the differential of $\varphi_P$ at $Q$ sends a
  tangent vector $t$ to the linear form $\omega \mapsto \omega_Q(t)$, so the invariant form with value
  $\lambda \mapsto \lambda(\omega)$ at the origin pulls back to $\omega$;
- the invariance of all holomorphic $1$-forms on the complex torus $J(X)$, so that these are all of $D_{J(X)}$, and a
  dimension count, both spaces having dimension the genus of $X$;
- the independence of $P$: $\varphi_{P'}$ is $\varphi_P$ followed by a translation, which fixes the invariant forms;
- or, algebraically, Milne's Proposition 2.2 for the canonical map $f^P$ of a curve into its Jacobian variety,
  carried to $\varphi_P$ by the comparison of the analytic and algebraic Jacobians (his Theorem 2.5).

## Sources

- G. Shimura, *On the factors of the jacobian variety of a modular function field*, J. Math. Soc.
  Japan 25 (1973), 523–544, <https://doi.org/10.2969/jmsj/02530523>: §1, p. 525 (the map $\psi$ through "a canonical
  map of $\mathfrak{H}^*/\Gamma$ into $J$", and $\delta\psi$); §3, p. 530 ($J$ identified with $Y_J/L_J$, and the
  canonical map of $\mathfrak{H}^*/\Gamma$ into $J$ induced by $z \mapsto \varphi_z$, $\varphi_z(\mu(g)) = \int_{z_0}^z g(z)\,dz$).
- J. S. Milne, "Jacobian varieties", in *Arithmetic Geometry* (G. Cornell and J. H. Silverman, eds.), Springer, 1986,
  167–212, <https://www.jmilne.org/math/articles/1986c.pdf>: Proposition 2.2, p. 172 (the map
  $(f^P)^* \colon \Gamma(J, \Omega^1_J) \to \Gamma(C, \Omega^1_C)$ is an isomorphism), with, on the same page, the
  composite of $f^P$ with a translation that gives $f^{P'}$; p. 173 (the analytic Jacobian
  $\Gamma(C(\mathbb{C}), \Omega^1)^\vee / H_1(C(\mathbb{C}), \mathbb{Z})$ and the map $g^P$ by integration, and
  Theorem 2.5).
