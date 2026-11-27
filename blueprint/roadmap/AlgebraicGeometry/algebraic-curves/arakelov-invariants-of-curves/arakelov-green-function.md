# Arakelov $(1,1)$-form and Arakelov–Green function

This node is still to be broken down. Let $X$ be a compact connected Riemann surface of
[genus](../jacobians-of-compact-riemann-surfaces/genus.md) $g \ge 1$. The space
$H^0(X, \Omega^1_X)$ of holomorphic differentials carries the hermitian inner product
$(\omega, \eta) \mapsto \frac{i}{2} \int_X \omega \wedge \overline{\eta}$. For an orthonormal basis
$(\omega_1, \ldots, \omega_g)$ of it, the **Arakelov $(1,1)$-form** is

$$\mu = \frac{i}{2g} \sum_{k=1}^g \omega_k \wedge \overline{\omega_k},$$

a smooth positive real-valued $(1,1)$-form on $X$ that does not depend on the orthonormal basis
and satisfies $\int_X \mu = 1$.

For a smooth nonnegative $(1,1)$-form $\mu$ on $X$ with $\int_X \mu = 1$, let $*$ be the star
operator on $1$-forms, given in a holomorphic coordinate $z = x + iy$ by $*dx = dy$ and
$*dy = -dx$. The **Green function** for $\mu$ is the unique smooth function
$\mathrm{gr}_\mu \colon (X \times X) \setminus \Delta \to \mathbb{R}$, with a logarithmic
singularity along the diagonal $\Delta$, such that for every fixed $w \in X$, in the sense of
distributions,

$$\frac{1}{2\pi} \, d * d \, \mathrm{gr}_\mu(z, w) = \delta_w(z) - \mu(z) \quad\text{and}\quad
\int_{z \in X \setminus \{w\}} \mathrm{gr}_\mu(z, w) \, \mu(z) = 0.$$

The **Arakelov–Green function** $\mathrm{gr}_X$ is the Green function for the Arakelov
$(1,1)$-form. It defines the **Arakelov metrics**: for a divisor $D = \sum_P n_P P$ on $X$, the
metric on $\mathcal{O}_X(D)$ with $\log \lVert 1 \rVert(Q) = \mathrm{gr}_X(D, Q) := \sum_P n_P \,
\mathrm{gr}_X(P, Q)$ for $Q$ outside the support of $D$, and the metric $\lVert \cdot
\rVert_{\mathrm{Ar}}$ on $\Omega^1_X$ given, for a local coordinate $z$ at a point $a$, by

$$-\log \lVert dz \rVert_{\mathrm{Ar}}(a) = \lim_{b \to a} \bigl( \mathrm{gr}_X(a, b) - \log
\lvert z(a) - z(b) \rvert \bigr).$$

## Depends on

- [Genus of a compact Riemann surface](../jacobians-of-compact-riemann-surfaces/genus.md)

## Proof depends on

Its proof uses the inputs listed under Expansion.

## Expansion

A good expansion has pages for: the hermitian inner product on holomorphic differentials and the
positivity of $\mu$; the existence and uniqueness of the Green function for a smooth nonnegative
$(1,1)$-form of total mass $1$; and the existence of the limit defining the Arakelov metric on
$\Omega^1_X$, with the curvature of the Arakelov metrics (Arakelov 1974, as cited by Javanpeykar,
§2.1, p. 94; not read here).

## Sources

- A. Javanpeykar, *Polynomial bounds for Arakelov invariants of Belyi curves*, Algebra Number Theory 8 (2014), 89–140, <https://doi.org/10.2140/ant.2014.8.89>, §2.1, pp. 93–94 (Arakelov $(1,1)$-form, Arakelov metrics).
- P. Bruin, *Appendix: Merkl's method of bounding Green functions*, in A. Javanpeykar, *Polynomial bounds for Arakelov invariants of Belyi curves*, Algebra Number Theory 8 (2014), 89–140, pp. 126–137, <https://doi.org/10.2140/ant.2014.8.89>, p. 126 (Green function for $\mu$).
