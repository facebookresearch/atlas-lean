# The principal polarization of an elliptic curve

This node is still to be broken down. It covers the identification of an elliptic curve with its dual abelian
variety through the divisor of its origin, which lets the results on abelian varieties and their duals, such as the
[Cassels–Tate pairing](../../NumberTheory/arithmetic-geometry/cassels-tate-pairing/cassels-tate-pairing-of-an-abelian-variety.md),
be applied to an elliptic curve.

Let $E$ be an elliptic curve over a field $K$, given by a nonsingular Weierstrass equation, with origin the point
$O$ at infinity, and let $\bar K$ be an algebraic closure of $K$.

1. $E$, with the chord-and-tangent group law, is an
   [abelian variety](../abelian-varieties/abelian-scheme.md) of dimension $1$ over $K$ with zero $O$.
2. The line bundle $L = \mathcal{O}_E((O))$ of the $K$-rational divisor $(O)$ is ample, and the homomorphism
   $\varphi_L \colon E \to E^\vee$ to the [dual abelian variety](../abelian-varieties/dual-abelian-variety.md),
   $P \mapsto t_P^* L \otimes L^{-1}$, is an isomorphism: a principal
   [polarization](../abelian-varieties/polarization.md) of $E$, defined over $K$ and coming from a line bundle on $E$
   over $K$. On points, $\varphi_L(P)$ is the class of $(-P) - (O)$ in
   $\operatorname{Pic}^0(E_{\bar K}) = E^\vee(\bar K)$.
3. Equivalently, every divisor of degree $0$ on $E_{\bar K}$ is linearly equivalent to $(P) - (O)$ for exactly one
   $P \in E(\bar K)$, and $P \mapsto$ the class of $(P) - (O)$ is an isomorphism of $\operatorname{Gal}(\bar K/K)$-modules
   $E(\bar K) \to \operatorname{Pic}^0(E_{\bar K})$, compatible with the group law.

Consequently $\varphi_L$ induces isomorphisms $H^1(K, E) \to H^1(K, E^\vee)$ and, for a number field $K$,
$\text{Ш}(K, E) \to \text{Ш}(K, E^\vee)$, and identifies the Weil pairing $e_n$ on $E[n] \times E^\vee[n]$ with a pairing
on $E[n]$.

## Expansion

A good expansion has pages for:

- the Riemann–Roch theorem for a curve of genus $1$, $\ell(D) = \deg D$ for $\deg D \ge 1$, from which item 3 follows
  (Silverman, Proposition III.3.4, using Corollary II.5.5);
- the group law of a Weierstrass cubic as a morphism, which makes $E$ a group variety and so, being a smooth
  projective connected curve, an abelian variety (Silverman, Theorem III.3.6);
- the ampleness of a divisor of positive degree on a smooth projective curve, and the identification of
  $E^\vee(\bar K)$ with $\operatorname{Pic}^0(E_{\bar K})$ (its item 1 on the dual abelian variety), which turn item 3 into
  item 2.

## Depends on

- [Abelian scheme](../abelian-varieties/abelian-scheme.md), for abelian varieties
- [Dual abelian variety](../abelian-varieties/dual-abelian-variety.md), for $E^\vee$ and $\varphi_L$ (its items 1 and 2)
- [Polarization](../abelian-varieties/polarization.md), for principal polarizations

## Proof depends on

- [Standard results of coherent cohomology on projective varieties](../birational-geometry/standard-results-of-coherent-cohomology.md), for the Riemann–Roch polynomial and Serre duality behind the Riemann–Roch theorem on the curve $E$
- [Dual abelian variety](../abelian-varieties/dual-abelian-variety.md), for $E^\vee(\bar K) = \operatorname{Pic}^0(E_{\bar K})$ (its item 1) and the isogeny $\varphi_L$ for ample $L$ (its item 2)
- [Abelian varieties are projective](../abelian-varieties/abelian-varieties-are-projective.md), for ample divisors on abelian varieties

## Sources

- J. H. Silverman, *The Arithmetic of Elliptic Curves*, 2nd ed., Graduate Texts in Mathematics 106, Springer, 2009:
  Chapter III, Proposition 3.4 (item 3), and Theorem 3.6 (the group law is a morphism); Chapter II,
  Corollary 5.5 (Riemann–Roch in genus $1$).
- B. Poonen and M. Stoll, *The Cassels-Tate pairing on polarized abelian varieties*, Ann. of Math. (2) 150 (1999),
  1109–1149, doi:10.2307/121064: Introduction, p. 1110 (for an elliptic curve the pairing on $\text{Ш}(E)$ is
  alternating, by Cassels), §2, p. 1114 (the convention $\varphi_L(a) = t_a^* L \otimes L^{-1}$), and Corollary 4 (p. 1120,
  the canonical polarization of a Jacobian, which for genus $1$ is $E$ itself, comes from a rational divisor on a
  homogeneous space).
- J. S. Milne, *Arithmetic Duality Theorems*, 2nd ed., 2006, <https://www.jmilne.org/math/Books/ADTnot.pdf>:
  Chapter I, Remark 6.11 (p. 80, elliptic curves as the case of Cassels' original definition).
