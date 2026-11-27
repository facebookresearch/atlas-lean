# The principal polarization of an elliptic curve

This node is still to be broken down. It covers the identification of an elliptic curve with its dual abelian
variety through the divisor of its origin, which lets the results on abelian varieties and their duals, such as the
[Cassels–Tate pairing](../../NumberTheory/arithmetic-geometry/cassels-tate-pairing/construction-of-the-cassels-tate-pairing/cassels-tate-pairing-of-an-abelian-variety.md),
be applied to an elliptic curve.

Let $E$ be an elliptic curve over a field $K$, given by a nonsingular Weierstrass equation, with origin the point
$O$ at infinity, and let $\bar K$ be an algebraic closure of $K$.

1. $E$, with the chord-and-tangent group law, is an
   [abelian variety](../abelian-varieties/abelian-scheme.md) of dimension $1$ over $K$ with zero $O$.
2. The line bundle $L = \mathcal{O}_E((O))$ of the $K$-rational divisor $(O)$ is ample, and the homomorphism
   $\varphi_L \colon E \to E^\vee$ to the [dual abelian variety](../abelian-varieties/dual-abelian-variety.md),
   $P \mapsto t_P^* L \otimes L^{-1}$, is an isomorphism of abelian varieties over $K$: a principal
   [polarization](../abelian-varieties/polarization.md) of $E$, coming from a line bundle on $E$ over $K$. On points,
   since $t_P^* \mathcal{O}_E((O)) = \mathcal{O}_E((-P))$, $\varphi_L(P)$ is the class of $(-P) - (O)$ in
   $\operatorname{Pic}^0(E_{\bar K}) = E^\vee(\bar K)$.

Consequently $\varphi_L$ induces isomorphisms of $\operatorname{Gal}(\bar K/K)$-modules $E(\bar K) \to E^\vee(\bar K)$, of
groups $H^1(K, E) \to H^1(K, E^\vee)$ and, for a number field $K$, $\text{Ш}(K, E) \to \text{Ш}(K, E^\vee)$; and it
carries the Weil pairing $e_n$ on $E[n] \times E^\vee[n]$ to a pairing on $E[n]$.

That $\varphi_L$ is an isomorphism is proved by its degree, not on points: in characteristic $p$ a homomorphism that
is bijective on $\bar K$-points need not be an isomorphism (the relative Frobenius of $E$ has degree $p$). By
Mumford's Riemann–Roch theorem, $\deg \varphi_L = \chi(L)^2$ and $\chi(L) = (D^g)/g!$ for $L = \mathcal{O}(D)$; here
$g = 1$ and $D = (O)$, so $\chi(L) = \deg (O) = 1$ and $\varphi_L$ is an isogeny of degree $1$, hence an isomorphism.

## Expansion

A good expansion has pages for:

- the group law of a Weierstrass cubic as a morphism defined over $K$, which makes $E$ a group variety and so, being
  a smooth projective geometrically connected curve, an abelian variety (item 1; Milne, *Abelian Varieties*,
  Introduction, pp. 1–2, over an algebraically closed field, where the group structure transported from
  $\operatorname{Pic}^0(E)$ by $P \mapsto [P] - [O]$ "agrees with the structure defined by chords and tangents, and hence
  is defined by polynomials");
- the ampleness of $(O)$: the functions $1$, $x$, $y$, whose only pole is at $O$, of order at most $3$, give the
  Weierstrass embedding, so $3(O)$ is very ample and $(O)$ is ample (Milne, *Abelian Varieties*, Example I.6.5,
  p. 30);
- the degree argument above, with the vanishing of $\deg \varphi_L$ exactly when $\varphi_L$ is not an isogeny, as
  in the convention of the page on line bundles on abelian varieties.

## Depends on

- [Abelian scheme](../abelian-varieties/abelian-scheme.md), for abelian varieties
- [Dual abelian variety](../abelian-varieties/dual-abelian-variety.md), for $E^\vee$, $E^\vee(\bar K) = \operatorname{Pic}^0(E_{\bar K})$ and $\varphi_L$ (its items 1 and 2)
- [Polarization](../abelian-varieties/polarization.md), for principal polarizations

## Proof depends on

- [Line bundles on abelian varieties](../abelian-varieties/line-bundles-on-abelian-varieties.md), for Mumford's Riemann–Roch theorem $\chi(\mathcal{O}(D)) = (D^g)/g!$ and $\deg \varphi_L = \chi(L)^2$ (its item 2)
- [Dual abelian variety](../abelian-varieties/dual-abelian-variety.md), for $\varphi_L$ being an isogeny when $L$ is ample (its item 2)
- [Isogenies of abelian schemes](../abelian-varieties/isogenies-of-abelian-schemes.md), for the degree of an isogeny as the rank of $f_* \mathcal{O}$ (its item 1), so that an isogeny of degree $1$ is an isomorphism

## Sources

- J. S. Milne, *Elliptic Curves*, BookSurge, 2006, <https://www.jmilne.org/math/Books/ectext6.pdf>: Chapter I,
  Proposition 4.10, p. 35 (for a nonsingular projective curve $C$ of genus $1$ and $O \in C(k)$, the map
  $P \mapsto [P] - [O] \colon C(k) \to \operatorname{Pic}^0(C)$ is bijective), with the paragraph after it (the group
  structure it defines is the chord-and-tangent one).
- J. S. Milne, *Abelian Varieties*, course notes, version 2.00 (2008), <https://www.jmilne.org/math/CourseNotes/AV.pdf>:
  Introduction, pp. 1–3 (the equivalent definitions of an elliptic curve, pp. 1–2, and "In the case of an elliptic
  curve, $E^\vee = E$", p. 3); Chapter I, Example 6.5, p. 30 (the divisor of the zero element is ample).
- B. Poonen and M. Stoll, *The Cassels-Tate pairing on polarized abelian varieties*, Ann. of Math. (2) 150 (1999),
  1109–1149, doi:10.2307/121064: Introduction, p. 1110 (for an elliptic curve the pairing on $\text{Ш}(E)$ is
  alternating, by Cassels), and §2, p. 1114 (the convention $\varphi_L(a) = t_a^* L \otimes L^{-1}$, and principal
  polarizations as polarizations that are isomorphisms).
