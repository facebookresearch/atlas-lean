# The Heegner point of an elliptic curve over an imaginary quadratic field

Let $E$ be an elliptic curve over $\mathbb{Q}$ of conductor $N$ and fix a
[modular parametrization](../../modular-forms-q-series/modular-forms/modular-parametrization-of-an-elliptic-curve.md)
$\varphi \colon X_0(N) \to E$, defined over $\mathbb{Q}$, that maps the cusp $\infty$ to the origin. Let
$K \subset \mathbb{C}$ be an imaginary quadratic field of discriminant $D_K \ne -3, -4$, so that its ring of integers
$\mathcal{O}$ has unit group $\{\pm 1\}$, in which every prime factor of $N$ splits. Choose an ideal $\mathcal{N}$ of
$\mathcal{O}$ with $\mathcal{O}/\mathcal{N} \cong \mathbb{Z}/N\mathbb{Z}$, which exists as these primes split.

The complex tori $\mathbb{C}/\mathcal{O}$ and $\mathbb{C}/\mathcal{N}^{-1}$ are elliptic curves related by the cyclic
$N$-isogeny $\mathbb{C}/\mathcal{O} \to \mathbb{C}/\mathcal{N}^{-1}$ induced by the identity of $\mathbb{C}$, whose
kernel is $\mathcal{N}^{-1}/\mathcal{O} \cong \mathbb{Z}/N\mathbb{Z}$; so they define a point $x_1 \in X_0(N)(\mathbb{C})$.
The point $x_1$ is rational over the
[Hilbert class field](../../algebraic-number-theory/adeles-class-field-theory/hilbert-class-field/is-hilbert-class-field.md)
$K_1 \subset \mathbb{C}$ of $K$. Put $y_1 = \varphi(x_1) \in E(K_1)$. The **Heegner point** of $E$ over $K$ is

$$y_K = \operatorname{Tr}_{K_1/K}(y_1) = \sum_{\sigma \in \operatorname{Gal}(K_1/K)} \sigma(y_1) \in E(K),$$

the sum taken with the group law of $E$. If $\mathcal{N}'$ is another ideal with
$\mathcal{O}/\mathcal{N}' \cong \mathbb{Z}/N\mathbb{Z}$ and $y_K'$ is the point it gives, then $y_K' = \pm y_K$ plus a
torsion point of $E(K)$.

The page defines $y_K$ and asserts the two facts it rests on: that $x_1$ is rational over $K_1$, and that $y_K$
depends on $\mathcal{N}$ only up to sign and torsion.

Proof: the two facts are the [rationality of $x_1$ over $K_1$](rationality-of-heegner-points.md) and the
[independence of the choice of $\mathcal{N}$](independence-of-the-heegner-point-from-the-ideal.md), for discriminants of
either parity. The construction uses the
[ideal $\mathcal{N}$](../heegner-point-construction/exists-ideal-is-add-cyclic-quotient-of-h.md), the
[cyclic isogeny](../heegner-point-construction/heegner-isogeny-is-add-cyclic-ker.md) and the
[point $x_1$ of $X_0(N)$](complex-points-of-x0-n-as-cyclic-isogenies.md).

## Depends on

- [An ideal of index $N$ under the Heegner hypothesis](../heegner-point-construction/exists-ideal-is-add-cyclic-quotient-of-h.md), for $\mathcal{N}$
- [The Heegner isogeny is cyclic of degree $N$](../heegner-point-construction/heegner-isogeny-is-add-cyclic-ker.md), for the cyclic $N$-isogeny $\mathbb{C}/\mathcal{O} \to \mathbb{C}/\mathcal{N}^{-1}$
- [Complex points of $X_0(N)$ as cyclic $N$-isogenies](complex-points-of-x0-n-as-cyclic-isogenies.md), for the point $x_1$
- [Modular parametrization of an elliptic curve over $\mathbb{Q}$](../../modular-forms-q-series/modular-forms/modular-parametrization-of-an-elliptic-curve.md), for $\varphi$ and $X_0(N)$
- [Hilbert class field of a number field](../../algebraic-number-theory/adeles-class-field-theory/hilbert-class-field/is-hilbert-class-field.md), for $K_1$
- [Unit groups of imaginary quadratic fields](../../algebraic-number-theory/quadratic-fields/schatunowsky-type-theorems/imag-quadratic-units-is-cyclic-card.md), for the unit group $\{\pm 1\}$ of $\mathcal{O}$ when $D_K \ne -3, -4$, which the statement asserts

## Proof depends on

- [Heegner points are rational over the Hilbert class field](rationality-of-heegner-points.md), for $x_1 \in X_0(N)(K_1)$
- [The Heegner point does not depend on the ideal, up to sign and torsion](independence-of-the-heegner-point-from-the-ideal.md), for the other choices of $\mathcal{N}$

## Sources

- B. H. Gross, *Kolyvagin's work on modular elliptic curves*, in *L-functions and arithmetic* (Durham, 1989),
  London Math. Soc. Lecture Note Ser. 153, Cambridge Univ. Press, 1991, 235–256: §1, p. 235, which writes the
  discriminant of $K$ as $-D$ and assumes "$D \ne 3, 4$, so the integers $\mathcal{O}$ of $K$ have unit group
  $\mathcal{O}^\times = \langle \pm 1 \rangle$", defines $x_1$, $y_1 = \varphi(x_1)$ and $y_K = \operatorname{Tr}_{K_1/K}(y_1)$,
  and states "we have $y_K' = \pm y_K +$ (torsion)".
- B. H. Gross and D. B. Zagier, *Heegner points and derivatives of $L$-series*, Invent. Math. 84 (1986), 225–320:
  Chapter I, §3, p. 227 (Heegner points of discriminant $D$ on $X_0(N)$, their rationality over the Hilbert class
  field and the simply transitive action of $W \times \operatorname{Gal}(H/K)$ on them), and Chapter V, §2, p. 310
  (the point $P_K = \sum_{\sigma \in \operatorname{Gal}(H/K)} \pi(x)^\sigma$, "Up to sign, it is independent of the
  choice of the Heegner point $x$").
- H. Darmon, *Rational points on modular elliptic curves*, CBMS Regional Conference Series in Mathematics 101,
  American Mathematical Society, 2004; author's version,
  <https://www.math.mcgill.ca/darmon/pub/Articles/Research/36.NSF-CBMS/chapter.pdf>, cited by the page numbers
  printed in that version: Hypothesis 3.9 (the Heegner hypothesis), p. 35, and the point
  $P_K = \operatorname{Trace}_{H_1/K}(P_1)$, §3.7, p. 39.
