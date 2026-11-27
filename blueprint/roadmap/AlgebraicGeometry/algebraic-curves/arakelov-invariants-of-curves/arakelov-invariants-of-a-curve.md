# Arakelov invariants of a curve over $\overline{\mathbb{Q}}$

This node is still to be broken down. Let $X$ be a smooth projective connected curve over
$\overline{\mathbb{Q}}$ of genus $g \ge 1$, and let $K$ be a number field, with a chosen embedding
$K \to \overline{\mathbb{Q}}$, such that $X$ has a semistable minimal regular model $p \colon
\mathcal{X} \to \operatorname{Spec} \mathcal{O}_K$: an integral regular flat projective
$\mathcal{O}_K$-scheme of relative dimension $1$ with geometrically connected fibres and generic
fibre a model of $X$, whose geometric fibres are reduced with only ordinary double points, and
which contains no exceptional divisor. For an embedding $\sigma \colon K \to \mathbb{C}$ let
$\mathcal{X}_\sigma$ be the compact Riemann surface $\mathcal{X} \times_{\mathcal{O}_K, \sigma}
\mathbb{C}$, with its [Arakelov metrics](arakelov-green-function.md). Give the relative dualizing
sheaf $\omega = \omega_{\mathcal{X}/\mathcal{O}_K}$ the Arakelov metrics on its restrictions
$\Omega^1_{\mathcal{X}_\sigma}$.

- **Faltings' delta invariant.** For a compact connected Riemann surface $Y$ of genus $g \ge 1$
  and any line bundle $L$ of degree $g - 1$ on $Y$, the canonical isomorphism from the determinant
  of cohomology $\lambda(L) = \det H^0(Y, L) \otimes \det H^1(Y, L)^\vee$ to the fibre at $[L]$ of
  $\mathcal{O}(-\Theta)$ on $\operatorname{Pic}_{g-1}(Y)$ has a norm independent of $L$ when
  $\lambda(L)$ carries the Faltings metric (normalized so that the metric on $\lambda(\Omega^1_Y)
  = \det H^0(Y, \Omega^1_Y)$ is induced by the inner product $\frac{i}{2}\int \omega \wedge
  \overline{\eta}$) and $\mathcal{O}(\Theta)$ the metric given by $\lVert \vartheta \rVert(z;
  \tau) = (\det \Im \tau)^{1/4} \exp(-\pi \, {}^t y (\Im \tau)^{-1} y) \lvert \vartheta(z; \tau)
  \rvert$, $y = \Im z$; this norm is $\exp(\delta_{\mathrm{Fal}}(Y)/8)$. Then
  $\delta_{\mathrm{Fal}}(X) = \frac{1}{[K : \mathbb{Q}]} \sum_\sigma
  \delta_{\mathrm{Fal}}(\mathcal{X}_\sigma)$.
- **Self-intersection of the dualizing sheaf.** $e(X) = (\omega, \omega) / [K : \mathbb{Q}]$, for
  Arakelov's intersection pairing on the arithmetic surface $\mathcal{X}$.
- **Discriminant.** $\Delta(X) = \frac{1}{[K : \mathbb{Q}]} \sum_{\mathfrak{p}} \delta_{\mathfrak{p}}
  \log \# k(\mathfrak{p})$, over the maximal ideals $\mathfrak{p}$ of $\mathcal{O}_K$, where
  $\delta_{\mathfrak{p}}$ is the number of singular points of the geometric fibre of $p$ over
  $\mathfrak{p}$.
- **Height of a point.** For $b \in X(\overline{\mathbb{Q}})$ inducing a section $P$ of $p$,
  $h(b) = \widehat{\deg} \, P^* \omega / [K : \mathbb{Q}] = (P, \omega) / [K : \mathbb{Q}]$, with
  the pulled-back metric.
- **Arakelov norm of the Wronskian differential.** On a compact connected Riemann surface $Y$ of
  genus $g \ge 1$, let $(\omega_1, \ldots, \omega_g)$ be an orthonormal basis of $H^0(Y,
  \Omega^1_Y)$ and, in a local coordinate $z$, write $\omega_k = f_k \, dz$ and $W_z(\omega) =
  \det\bigl( \frac{1}{(l-1)!} \frac{d^{l-1} f_k}{dz^{l-1}} \bigr)_{1 \le k, l \le g}$. The
  differentials $W_z(\omega) (dz)^{\otimes g(g+1)/2}$ glue to a nonzero global section
  $\mathrm{Wr}$ of $(\Omega^1_Y)^{\otimes g(g+1)/2}$, independent of the choices; its divisor
  $\mathcal{W}$, the divisor of Weierstrass points, is effective of degree $g^3 - g$, and
  $\lVert \mathrm{Wr} \rVert_{\mathrm{Ar}}$ is its norm in the Arakelov metric. For $b \in
  X(\overline{\mathbb{Q}})$, $\lVert \mathrm{Wr} \rVert_{\mathrm{Ar}}(b) = \bigl( \prod_\sigma
  \lVert \mathrm{Wr} \rVert_{\mathrm{Ar}}(b_\sigma) \bigr)^{1/[K : \mathbb{Q}]}$.

These do not depend on the choice of $K$ and of the model. The
[Faltings height](../../abelian-varieties/stable-faltings-height/faltings-height.md)
$h_{\mathrm{Fal}}(X) = \widehat{\deg} \det p_* \omega / [K : \mathbb{Q}]$, with the Faltings
metric on the determinant of cohomology, is the stable Faltings height of the Jacobian of
$\mathcal{X}_K$.

## Depends on

- [Arakelov $(1,1)$-form and Arakelov–Green function](arakelov-green-function.md), for the
  Arakelov metrics
- [Stable Faltings height](../../abelian-varieties/stable-faltings-height/faltings-height.md), for
  the comparison with $h_{\mathrm{Fal}}(X)$

## Proof depends on

Its proof uses the inputs listed under Expansion.

## Expansion

A good expansion has pages for: semistable minimal regular models of curves over number fields
and their existence after a finite extension (Liu, Theorems 10.1.8, 10.3.34(a) and 10.4.3, as cited
by Javanpeykar, p. 97); Arakelov divisors and Arakelov's intersection pairing on an arithmetic
surface, with the admissibility of $\omega$ (§2.2, pp. 95–97); the Faltings metric on the
determinant of cohomology and the constancy of the norm defining $\delta_{\mathrm{Fal}}$
(Faltings 1984, Theorem 1 and Section 3, as cited on pp. 94–95); the Wronskian differential and the
degree of the divisor of Weierstrass points; the independence of $K$ and of the model
(Moret-Bailly 1990, Section 5.4, as cited on p. 98); and the comparison of $h_{\mathrm{Fal}}(X)$
with the stable Faltings height of the Jacobian (L. Szpiro (ed.), Astérisque 127, 1985, Chapter I, Lemma 3.2.1, as
cited on p. 98). The sources cited only through Javanpeykar were not read here.

## Sources

- A. Javanpeykar, *Polynomial bounds for Arakelov invariants of Belyi curves*, Algebra Number Theory 8 (2014), 89–140, <https://doi.org/10.2140/ant.2014.8.89>, §2.1, pp. 93–95 (Faltings metric, $\delta_{\mathrm{Fal}}$ of a Riemann surface,
  Wronskian differential), §2.2, pp. 95–97 (arithmetic surfaces, Definition 2.2.1), and §2.3,
  pp. 97–98 (the invariants of $X$).
