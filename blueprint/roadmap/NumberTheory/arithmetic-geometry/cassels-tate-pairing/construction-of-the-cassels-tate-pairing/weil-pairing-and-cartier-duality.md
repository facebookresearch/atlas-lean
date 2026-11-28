# The Weil pairing and the Cartier duality of A[m] and its dual

Let $k$ be a field, $m \ge 1$ an integer not divisible by the characteristic of $k$, $A$ an
[abelian variety](../../../../AlgebraicGeometry/abelian-varieties/abelian-scheme.md) over $k$ and $A^\vee$ its
[dual](../../../../AlgebraicGeometry/abelian-varieties/dual-abelian-variety.md). Let
$\langle\,,\rangle_m \colon A[m](\bar k) \times A^\vee[m](\bar k) \to \mu_m(\bar k)$ be the pairing given by the canonical
identification of $A^\vee[m]$ with the Cartier dual of $A[m]$ (item 3 of the page on the dual abelian variety), and
$e_m$ the [Weil pairing through a Poincaré divisor](weil-pairing-through-a-poincare-divisor.md).

1. There is a sign $\varepsilon \in \{1, -1\}$ such that $e_m(x, x') = \langle x, x'\rangle_m^{\varepsilon}$ for all
   $x \in A[m](\bar k)$ and $x' \in A^\vee[m](\bar k)$. In particular $e_m$ is perfect: it identifies $A^\vee[m](\bar k)$
   with $\operatorname{Hom}(A[m](\bar k), \mu_m(\bar k))$ as Galois modules.
2. If $k$ is a finite extension of $\mathbb{Q}_p$ or $k = \mathbb{R}$, the cup product through $e_m$,
   $H^1(k, A[m]) \times H^1(k, A^\vee[m]) \to H^2(k, \bar k^\times) = \mathrm{Br}(k)$, vanishes on the product of the images of
   the Kummer maps $A(k) \to H^1(k, A[m])$ and $A^\vee(k) \to H^1(k, A^\vee[m])$.

For 2 over a $p$-adic field, take the pairing through $\langle\,,\rangle_m$ instead, which by 1 changes the cup product by the
sign $\varepsilon$: by the compatibility of local duality for abelian varieties with the finite-level dualities, the
cup product of the Kummer image of $P' \in A^\vee(k)$ with a class $c \in H^1(k, A[m])$ is the local pairing of $P'$ with
the image of $c$ in $H^1(k, A)$, which is $0$ when $c$ is a Kummer image.

## Expansion

This node is still to be broken down. A good expansion states and links:

- a description of $\langle\,,\rangle_m$ by functions: for $x' \in A^\vee[m]$ given by a line bundle $L$ in
  $\operatorname{Pic}^0$, a trivialization of $[m]^* L$ and its translates by the points of $A[m]$;
- its comparison with the divisor formula of $e_m$, by Lang's reciprocity law, which gives 1;
- the orthogonality in 2 over $\mathbb{R}$, from the diagram of Kummer sequences for $n = 2$ in Milne's Remark I.3.7 and the
  analogous compatibility there.

## Depends on

- [The Weil pairing through a Poincaré divisor](weil-pairing-through-a-poincare-divisor.md)
- [Dual abelian variety](../../../../AlgebraicGeometry/abelian-varieties/dual-abelian-variety.md), for the Cartier duality of $A[m]$ and $A^\vee[m]$ (its item 3)
- [Local class field theory: cohomology and the existence theorem](../../../p-adic-numbers/local-class-field-theory-cohomology.md), for $\mathrm{Br}(k) = H^2(k, \bar k^\times)$ (its item 2)
- [Cohomology of profinite groups](../../../../RepresentationTheory/group-cohomology/cohomology-of-profinite-groups.md), for cup products (its item 3)

## Proof depends on

- [Lang's reciprocity law for divisors on a product](lang-reciprocity-law.md)
- [Tate local duality for abelian varieties](../../../algebraic-number-theory/galois-representations/galois-cohomology-of-local-fields/tate-local-duality-for-abelian-varieties.md), for the compatibility of the local pairing with the finite-level pairings through $\langle\,,\rangle_m$ (its item 3) and the real case (its item 4)

## Sources

- J. S. Milne, *Arithmetic Duality Theorems*, 2nd ed., 2006, <https://www.jmilne.org/math/Books/ADTnot.pdf>:
  Chapter I, Remark 3.5, p. 44 (the local pairings defined through a Poincaré divisor "agree with those in (3.4) (up to
  sign)", checked through their compatibility with the pairings defined by the $e_n$-pairing $A^t_n \times A_n \to \mathbb{G}_m$),
  and Remark 3.7, p. 46 (the real case).
- B. Poonen and M. Stoll, *The Cassels-Tate pairing on polarized abelian varieties*, Ann. of Math. (2) 150 (1999),
  1109–1149, doi:10.2307/121064: §12.2, footnote 21, p. 1143 (the normalization of $e_m$, "the inverse of that in [La1]").
- S. Lang, *Abelian Varieties*, Springer-Verlag, 1983, p. 173, as cited by Poonen and Stoll, §12.2, p. 1143; not read.
