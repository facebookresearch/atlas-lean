# Analytic continuation and functional equation of the $L$-function of an elliptic curve over $\mathbb{Q}$

Let $E$ be an elliptic curve over $\mathbb{Q}$ of conductor $N$, with
$L$-function $L(E, s) = \sum_{n \ge 1} a_n n^{-s}$, the Euler product of
[modularity of elliptic curves over $\mathbb{Q}$](../../../AlgebraicGeometry/elliptic-curves/modularity-of-elliptic-curves-over-q.md),
which converges for $\operatorname{Re}(s) > 3/2$. Let $f$ be the newform of weight $2$ and level $N$ with
$L(f, s) = L(E, s)$ that the modularity theorem provides.

1. **Continuation and functional equation.** $L(E, s)$ extends to an entire function on $\mathbb{C}$, and

    $$\Lambda(E, s) = (2\pi)^{-s} \Gamma(s) N^{s/2} L(E, s)$$

    satisfies $\Lambda(E, s) = w(E) \, \Lambda(E, 2 - s)$ for a sign $w(E) \in \{1, -1\}$, the **root number** of $E$.
2. **The sign.** Let $w_N$ be the Fricke involution of the
   [modular curve](../../modular-forms-q-series/modular-forms/modular-curve-of-a-group-of-level-n.md)
   $X_0(N) = X_{\Gamma_0(N)}$ over $\mathbb{Q}$, which sends a cyclic $N$-isogeny
   $\varphi \colon A \to A'$ to its dual $\varphi' \colon A' \to A$, and let $\varepsilon \in \{1, -1\}$ be its
   eigenvalue on the differential $\omega_f = 2\pi i f(z) \, dz$, that is, $w_N^* \omega_f = \varepsilon \omega_f$.
   Then $w(E) = -\varepsilon$.
3. **Parity.** Consequently $L(E, s)$ vanishes to even order at $s = 1$ when $w(E) = 1$ and to odd order when
   $w(E) = -1$. In particular, if $L(E, s)$ has a simple zero at $s = 1$, then $w(E) = -1$.

Proof, from the pages beside this one: by modularity
$L(E, s) = L(f, s)$, so $\Lambda(E, s) = \Lambda(f, s)$, the [Mellin transform](mellin-transform-of-a-weight-two-cusp-form.md)
of $f$ on the half-plane where the Euler product converges, and the
[functional equation of $L(f, s)$](functional-equation-of-the-l-function-of-a-newform.md) gives
items 1 and 2 with $w(E) = -\varepsilon$, $\varepsilon$ the [Fricke eigenvalue](fricke-eigenvalue-of-a-newform.md)
of $f$, normalised by $w_N^*\omega_f = \varepsilon\omega_f$ as in item 2. For item 3 (worked out here; Darmon states the conclusion,
p. 21): $\Lambda(E, s)$ is not identically zero, as $a_1 = 1$ and so $L(E, s) \to 1$ as $s \to +\infty$ along the real
axis; as $(2\pi)^{-s}\Gamma(s)N^{s/2}$ is holomorphic and nonzero at $s = 1$ ($\Gamma(1) = 1$), $L(E, s)$ and
$\Lambda(E, s)$ vanish to the same order $m$ there. Writing $\Lambda(E, 1 + h) = \sum_{k \ge 0} c_k h^k$, the functional
equation gives $c_k = w(E)(-1)^k c_k$ for every $k$, and $c_m \ne 0$ forces $(-1)^m = w(E)$.

## Depends on

- [Modularity of elliptic curves over $\mathbb{Q}$](../../../AlgebraicGeometry/elliptic-curves/modularity-of-elliptic-curves-over-q.md), for $L(E, s)$ and the newform $f$ of item 2
- [Modular curve of a group of level $N$ and its standard model over $\mathbb{Q}$](../../modular-forms-q-series/modular-forms/modular-curve-of-a-group-of-level-n.md), for $X_0(N) = X_{\Gamma_0(N)}$ over $\mathbb{Q}$, on which $w_N$ acts in item 2
- [Fricke eigenvalue of a newform](fricke-eigenvalue-of-a-newform.md), for the eigenvalue $\varepsilon$ of item 2 and its description by $w_N^*\omega_f = \varepsilon\omega_f$

## Proof depends on

- [Modularity of elliptic curves over $\mathbb{Q}$](../../../AlgebraicGeometry/elliptic-curves/modularity-of-elliptic-curves-over-q.md), for $L(E, s) = L(f, s)$
- [Mellin transform of a weight-two cusp form](mellin-transform-of-a-weight-two-cusp-form.md), for $\Lambda(f, s)$ as an integral
- [Functional equation of the $L$-function of a newform](functional-equation-of-the-l-function-of-a-newform.md), for the continuation and $\Lambda(f, s) = -\varepsilon\Lambda(f, 2 - s)$

## Sources

- H. Darmon, *Rational points on modular elliptic curves*, CBMS Regional Conference Series in Mathematics 101,
  American Mathematical Society, 2004; author's version,
  <https://www.math.mcgill.ca/darmon/pub/Articles/Research/36.NSF-CBMS/chapter.pdf>, cited by the page numbers
  printed in that version: Theorem 1.13 ("The $L$-function $L(E, s)$ extends to an entire function on $\mathbb{C}$
  and has a functional equation relating its value at $s$ and $2 - s$, of the form $\Lambda(E, s) = \pm\Lambda(E, 2 - s)$,
  where $\Lambda(E, s) := (2\pi)^{-s}\Gamma(s)N^{s/2}L(E, s)$"), pp. 8–9; (2.11)–(2.14), pp. 17–18; Corollary 2.15,
  (2.17) and the sentence after it ("$L(E, s)$ vanishes to even (resp. odd) order at $s = 1$ when
  $\operatorname{sign}(E, \mathbb{Q}) = 1$ (resp. $\operatorname{sign}(E, \mathbb{Q}) = -1$)"), pp. 20–21.
- B. H. Gross, *Kolyvagin's work on modular elliptic curves*, in *L-functions and arithmetic* (Durham, 1989),
  London Math. Soc. Lecture Note Ser. 153, Cambridge Univ. Press, 1991, 235–256: (5.2) and the sentence after it,
  p. 243 ("Let $\epsilon = \pm 1$ be the eigenvalue of the Fricke involution $w_N$ on the eigenform $f$ … Then the
  $L$-function of $E$ over $\mathbb{Q}$ satisfies a functional equation with sign $= -\epsilon$.").
- J. Coates, *The work of Gross and Zagier on Heegner points and the derivatives of $L$-series*, Séminaire Bourbaki,
  exp. 635 (1984/85), Astérisque 133–134 (1986), 57–72, <http://www.numdam.org/item?id=SB_1984-1985__27__57_0>:
  the functional equation (6), p. 64, written with $\Lambda(E, s) = (2\pi)^{-s}\Gamma(s)L(E, s)$ as
  $\Lambda(E, s) = w_E N^{1-s} \Lambda(E, 2 - s)$, $w_E = \pm 1$.
- B. H. Gross and D. B. Zagier, *Heegner points and derivatives of $L$-series*, Invent. Math. 84 (1986), 225–320:
  Chapter I, §2, (2.1), p. 227, for the involution $w_N$ of $X_0(N)$.
