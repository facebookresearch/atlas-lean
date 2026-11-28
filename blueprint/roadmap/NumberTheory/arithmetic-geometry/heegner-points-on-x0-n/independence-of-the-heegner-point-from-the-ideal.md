# The Heegner point does not depend on the ideal, up to sign and torsion

Let $E$ be an elliptic curve over $\mathbb{Q}$ of conductor $N$, let $\varphi \colon X_0(N) \to E$ be a
[modular parametrization](../../modular-forms-q-series/modular-forms/modular-parametrization-of-an-elliptic-curve.md)
with $\varphi(\infty) = O$, and let $K \subset \mathbb{C}$ be an imaginary quadratic field of discriminant
$D_K \ne -3, -4$, odd or even, in which every prime factor of $N$ splits, with
[Hilbert class field](../../algebraic-number-theory/adeles-class-field-theory/hilbert-class-field/is-hilbert-class-field.md)
$K_1$. For an ideal $\mathcal{N}$ of $\mathcal{O}_K$ with $\mathcal{O}_K/\mathcal{N} \cong \mathbb{Z}/N\mathbb{Z}$, let
$x_{\mathcal{N}} \in X_0(N)(K_1)$ be the [point](rationality-of-heegner-points.md) of the cyclic $N$-isogeny
$\mathbb{C}/\mathcal{O}_K \to \mathbb{C}/\mathcal{N}^{-1}$, and let
$y_{\mathcal{N}} = \operatorname{Tr}_{K_1/K} \varphi(x_{\mathcal{N}}) \in E(K)$. If $\mathcal{N}'$ is another such ideal, then

$$y_{\mathcal{N}'} = \pm\, y_{\mathcal{N}} + t \qquad \text{for a torsion point } t \in E(K).$$

## Expansion

This node is still to be broken down. A good expansion states and links:

- the ideals $\mathcal{N}'$ with $\mathcal{O}_K/\mathcal{N}' \cong \mathbb{Z}/N\mathbb{Z}$: writing $p\mathcal{O}_K = P_p \bar{P}_p$ for
  $p \mid N$ and $p^{e_p} \parallel N$, each is divisible by exactly one of $P_p^{e_p}$ and $\bar{P}_p^{e_p}$, so that
  $\mathcal{N}' = \mathcal{N}_{N/d}\,\bar{\mathcal{N}}_d$, where $d \mid N$, $\gcd(d, N/d) = 1$, collects the primes at
  which $\mathcal{N}'$ and $\mathcal{N}$ differ and $\mathcal{N}_m$ is the part of $\mathcal{N}$ of norm $m$;
- the identity $x_{\mathcal{N}'} = w_d(x_{\mathcal{N}}^{\sigma})$, for the Atkin–Lehner involution $w_d$ of Gross and
  Zagier's (2.2) and the element $\sigma \in \operatorname{Gal}(K_1/K)$ attached to the class of $\mathcal{N}_d$ by the
  main theorem of complex multiplication (Darmon, Theorems 3.5 and 3.7), worked out on the cyclic isogenies
  $\mathbb{C}/\mathfrak{a} \to \mathbb{C}/\mathfrak{a}\mathcal{N}^{-1}$;
- the conclusion: by [the Atkin–Lehner involutions on the parametrization](../complex-conjugation-and-the-trace/atkin-lehner-involutions-on-a-modular-parametrization.md),
  $\varphi(x_{\mathcal{N}'}) = \varepsilon_d\,\varphi(x_{\mathcal{N}})^{\sigma} + P_d$ with $P_d \in E(\mathbb{Q})$ of
  finite order, and the trace over $\operatorname{Gal}(K_1/K)$ gives the statement with the sign $\varepsilon_d$.

For odd $D_K$ the identity of the second item is a case of the simple transitivity of
[the Galois and Atkin–Lehner action on Heegner points](galois-and-atkin-lehner-action-on-heegner-points.md).

## Depends on

- [Modular parametrization of an elliptic curve over $\mathbb{Q}$](../../modular-forms-q-series/modular-forms/modular-parametrization-of-an-elliptic-curve.md), for $\varphi$
- [Hilbert class field of a number field](../../algebraic-number-theory/adeles-class-field-theory/hilbert-class-field/is-hilbert-class-field.md), for $K_1$
- [Heegner points are rational over the Hilbert class field](rationality-of-heegner-points.md), for the points $x_{\mathcal{N}} \in X_0(N)(K_1)$

## Proof depends on

- [Decomposition of rational primes in a quadratic field](../../algebraic-number-theory/quadratic-fields/quadratic-field-prime-decomposition.md), for the factorisation $p\mathcal{O}_K = P_p\bar{P}_p$ of the primes dividing $N$, which describes the ideals $\mathcal{N}'$
- [Main theorem of complex multiplication for elliptic curves](../../algebraic-number-theory/adeles-class-field-theory/hilbert-class-field/main-theorem-of-complex-multiplication.md), for the action of $\operatorname{Gal}(K_1/K)$ on the curves $\mathbb{C}/\mathfrak{a}$ through the class group, for every discriminant
- [Atkin–Lehner involutions on a modular parametrization](../complex-conjugation-and-the-trace/atkin-lehner-involutions-on-a-modular-parametrization.md), for $\varphi \circ w_d = \varepsilon_d\,\varphi + P_d$

The rest of its proof is that of the sources below, as the Expansion describes.

## Sources

- B. H. Gross, *Kolyvagin's work on modular elliptic curves*, in *L-functions and arithmetic* (Durham, 1989),
  London Math. Soc. Lecture Note Ser. 153, Cambridge Univ. Press, 1991, 235–256: §1, p. 235, for every imaginary quadratic field of discriminant $-D$ with $D \ne 3, 4$ in which the
  prime factors of $N$ split, with no condition on the parity of $D$ ("we have $y_K' = \pm y_K +$ (torsion)").
- B. H. Gross and D. B. Zagier, *Heegner points and derivatives of $L$-series*, Invent. Math. 84 (1986), 225–320: Chapter V, §2, p. 310 ("Up to sign, it is independent of the choice of the Heegner point $x$"), under the
  standing assumption of Chapter I, §3, p. 227, that $D$ is odd; Chapter I, §2, (2.2), p. 227, the involutions $w_d$.
- H. Darmon, *Rational points on modular elliptic curves*, CBMS Regional Conference Series in Mathematics 101,
  American Mathematical Society, 2004; author's version,
  <https://www.math.mcgill.ca/darmon/pub/Articles/Research/36.NSF-CBMS/chapter.pdf>, cited by the page numbers
  printed in that version: Theorem 3.5, p. 33, and Theorem 3.7 (Shimura reciprocity law), p. 34, for orders of every discriminant.
- C. Delaunay, *Critical and ramification points of the modular parametrization of an elliptic curve*,
  J. Théor. Nombres Bordeaux 17 (2005), 109–124: §2, p. 112, the involutions $W_Q$ on the modular parametrization.
