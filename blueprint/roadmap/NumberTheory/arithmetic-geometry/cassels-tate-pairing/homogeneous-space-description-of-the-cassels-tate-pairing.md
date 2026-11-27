# The homogeneous space description of the Cassels–Tate pairing

This is the comparison, due to Poonen and Stoll, of the
[Cassels–Tate pairing](cassels-tate-pairing-of-an-abelian-variety.md) with its description through principal
homogeneous spaces, which goes back to Cassels for elliptic curves and to Tate in general, and which the proof of
the [alternating property](alternating-property-of-the-cassels-tate-pairing.md) uses.

Let $K$ be a number field, $A$ an [abelian variety](../../../AlgebraicGeometry/abelian-varieties/abelian-scheme.md)
over $K$ with [dual](../../../AlgebraicGeometry/abelian-varieties/dual-abelian-variety.md) $A^\vee$, and let
$a \in \text{Ш}(K, A)$ and $a' \in \text{Ш}(K, A^\vee)$. Let $X$ be a principal homogeneous space of $A$ over $K$
whose class in $H^1(K, A)$ is $a$; it has a $K_v$-point for every place $v$. Write $K_s = \bar K$ and $K_s(X)$ for
the function field of $X_{K_s}$.

1. A trivialization $A_{K_s} \to X_{K_s}$, $Q \mapsto P + Q$, identifies $\operatorname{Pic}^0(X_{K_s})$ with
   $\operatorname{Pic}^0(A_{K_s}) = A^\vee(K_s)$, independently of the point $P \in X(K_s)$, since translations act
   trivially on $\operatorname{Pic}^0(A_{K_s})$; the identification is $G_K$-equivariant. So $a'$ gives a class in
   $H^1(G_K, \operatorname{Pic}^0(X_{K_s}))$.
2. Let $b' \in H^2(G_K, K_s(X)^\times/K_s^\times)$ be its image under the connecting map of
   $0 \to K_s(X)^\times/K_s^\times \to \operatorname{Div}^0(X_{K_s}) \to \operatorname{Pic}^0(X_{K_s}) \to 0$. As
   $H^3(G_K, K_s^\times) = 0$, $b'$ lifts to $f' \in H^2(G_K, K_s(X)^\times)$.
3. For every place $v$, the restriction $f'_v \in H^2(G_v, K_{v,s}(X)^\times)$ is the image of a unique
   $c_v \in \mathrm{Br}(K_v) = H^2(G_v, K_{v,s}^\times)$.
   - *Existence.* The image $a'_v$ of $a'$ in $H^1(G_v, \operatorname{Pic}^0(X_{K_{v,s}}))$ is zero, because $a'$ lies in
     $\text{Ш}(K, A^\vee)$. The image of $f'_v$ in $H^2(G_v, K_{v,s}(X)^\times/K_{v,s}^\times)$ is the restriction $b'_v$ of
     $b'$, which is the image of $a'_v$ under the local connecting map, hence zero. By the exactness of the local
     cohomology sequence of $1 \to K_{v,s}^\times \to K_{v,s}(X)^\times \to K_{v,s}(X)^\times/K_{v,s}^\times \to 1$,
     $f'_v$ comes from $\mathrm{Br}(K_v)$.
   - *Uniqueness.* Since $X$ has a $K_v$-point, the map $\mathrm{Br}(K_v) \to H^2(G_v, K_{v,s}(X)^\times)$ is
     [injective](proof-of-the-homogeneous-space-description/brauer-group-into-functions-on-a-torsor-with-a-point.md)
     (Milne, Remark I.6.11). One may then compute $c_v$ by evaluating $f'_v$ at a point of $X(K_v)$ away from its zeros
     and poles (Poonen–Stoll, §3.1, footnote 5).

   Only finitely many $c_v$ are nonzero: by the comparison below, the $c_v$ are the classes of the local terms of the
   Albanese–Picard definition (Poonen–Stoll, proof of Proposition 32), and Milne writes the family $(c_v)$ in the
   direct sum $\bigoplus_v \mathrm{Br}(K_v)$.

Then

$$\langle a, a' \rangle = \sum_v \mathrm{inv}_v(c_v),$$

where $\langle\,,\rangle$ is the Cassels–Tate pairing; in particular the right side does not depend on the choices of
$X$, $f'$ and the $c_v$. Poonen and Stoll prove this by comparing four definitions: the homogeneous space definition
above, the Albanese–Picard definition, the Albanese–Albanese definition for a Poincaré divisor $\mathcal{P}$, and the Weil
pairing definition. With $\mathcal{P}$ also used for $e_m$,

$$\langle a, a'\rangle = \langle a, a'\rangle_{\mathcal{P}} = \langle a, a'\rangle_A = \sum_v \mathrm{inv}_v(c_v),$$

by the agreement of the Weil pairing and Albanese–Albanese definitions, of the Albanese–Albanese and Albanese–Picard
definitions, and of the Albanese–Picard and homogeneous space definitions; see
[Proof of the homogeneous space description](proof-of-the-homogeneous-space-description/README.md).

## Depends on

- [The Cassels–Tate pairing of an abelian variety](cassels-tate-pairing-of-an-abelian-variety.md)
- [Dual abelian variety](../../../AlgebraicGeometry/abelian-varieties/dual-abelian-variety.md), for $A^\vee(K_s) = \operatorname{Pic}^0(A_{K_s})$ (its item 1)
- [Vanishing of the third cohomology of the multiplicative group of a number field](../../algebraic-number-theory/galois-representations/galois-cohomology-of-number-fields/vanishing-of-h3-of-the-multiplicative-group.md), for the lift $f'$
- [Local class field theory: cohomology and the existence theorem](../../p-adic-numbers/local-class-field-theory-cohomology.md), for the local invariant maps (its item 2)
- [Cohomology of profinite groups](../../../RepresentationTheory/group-cohomology/cohomology-of-profinite-groups.md), for the long exact sequences

## Proof depends on

- [The Albanese–Albanese and Weil pairing definitions agree](proof-of-the-homogeneous-space-description/albanese-albanese-and-weil-pairing-definitions-agree.md)
- [The Albanese–Albanese and Albanese–Picard definitions agree](proof-of-the-homogeneous-space-description/albanese-albanese-and-albanese-picard-definitions-agree.md)
- [The Albanese–Picard and homogeneous space definitions agree](proof-of-the-homogeneous-space-description/albanese-picard-and-homogeneous-space-definitions-agree.md)
- [The Brauer group of a local field embeds in the second cohomology of the functions on a torsor with a point](proof-of-the-homogeneous-space-description/brauer-group-into-functions-on-a-torsor-with-a-point.md), for the uniqueness in 3
- [Theorem of the cube, theorem of the square and the seesaw principle](../../../AlgebraicGeometry/abelian-varieties/theorem-of-the-cube.md), for the trivial action of translations on $\operatorname{Pic}^0(A_{K_s})$ in 1

## Sources

- B. Poonen and M. Stoll, *The Cassels-Tate pairing on polarized abelian varieties*, Ann. of Math. (2) 150 (1999),
  1109–1149, doi:10.2307/121064: §3.1, "The homogeneous space definition", p. 1115, with footnote 5 (evaluation at
  a point of $X(K_v)$); §3.2, "The Albanese-Picard definition", pp. 1115–1117; §12, "Appendix: Other definitions of
  the Cassels-Tate pairing", §§12.1–12.3, Propositions 31–34, pp. 1142–1147.
- J. S. Milne, *Arithmetic Duality Theorems*, 2nd ed., 2006, <https://www.jmilne.org/math/Books/ADTnot.pdf>:
  Chapter I, Remark 6.11 (pp. 80–81: the homogeneous space description, "which in the case of elliptic curves
  reduces to the original definition of Cassels 1962, §3", the vanishing of $H^3(G_K, K_s^\times)$ and the injectivity
  of $\mathrm{Br}(K_v) \to H^2(G_v, K_{v,s}(X)^\times)$ for a locally trivial $X$), and Remark 6.12 with footnote 16
  (pp. 81–82, a fourth description for Jacobians, and the reference to C. D. Gonzalez-Aviles, J. Math. Sci. Univ.
  Tokyo 10 (2003), 391–419, for its agreement with Proposition 6.9).
- S. Lang, *Abelian Varieties*, Chapter VI, §4, Theorem 10 (the reciprocity law), not read here: p. 171 of the
  Springer-Verlag edition of 1983, as cited by Poonen and Stoll ([La1], §2, p. 1114); Milne, Remark I.3.5, p. 44,
  cites the same theorem in the Interscience edition of 1959.
