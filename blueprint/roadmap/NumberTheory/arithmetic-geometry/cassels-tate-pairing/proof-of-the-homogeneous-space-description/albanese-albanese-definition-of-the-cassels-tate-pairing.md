# The Albanese–Albanese definition of the Cassels–Tate pairing

Let $K$ be a number field, $A$ an [abelian variety](../../../../AlgebraicGeometry/abelian-varieties/abelian-scheme.md) over
$K$ with [dual](../../../../AlgebraicGeometry/abelian-varieties/dual-abelian-variety.md) $A^\vee$, and $\mathcal{P}$ a
[Poincaré divisor](../construction-of-the-cassels-tate-pairing/weil-pairing-through-a-poincare-divisor.md) on $A \times A^\vee$.
Use the exact sequences

$$0 \to Y^0(A_{\bar K}) \to Z^0(A_{\bar K}) \to A(\bar K) \to 0, \qquad 0 \to Y^0(A^\vee_{\bar K}) \to Z^0(A^\vee_{\bar K}) \to A^\vee(\bar K) \to 0,$$

and the partially defined pairings $Y^0(A_{\bar K}) \times Z^0(A^\vee_{\bar K}) \to \bar K^\times$, $(\mathfrak{b}, \mathfrak{b}') \mapsto \mathcal{P}(\mathfrak{b}, \mathfrak{b}')$, and
$Z^0(A_{\bar K}) \times Y^0(A^\vee_{\bar K}) \to \bar K^\times$, $(\mathfrak{b}, \mathfrak{b}') \mapsto {}^t\mathcal{P}(\mathfrak{b}', \mathfrak{b})$, which agree on
$Y^0 \times Y^0$ by [Lang's reciprocity law](../construction-of-the-cassels-tate-pairing/lang-reciprocity-law.md); write $\cup$
for both, and likewise over each completion $K_v$. For $a \in \text{Ш}(K, A)$ and $a' \in \text{Ш}(K, A^\vee)$ the
**Albanese–Albanese pairing** $\langle a, a'\rangle_{\mathcal{P}} \in \mathbb{Q}/\mathbb{Z}$ is defined by the steps of the
[Albanese–Picard definition](albanese-picard-definition-of-the-cassels-tate-pairing.md), with $\mathfrak{a}'$ now a lift of a cocycle
of $a'$ to $C^1(G_K, Z^0(A^\vee_{\bar K}))$, all lifts chosen, as there, so that every value used is defined (a value
$\mathcal{P}(\mathfrak{b}, \mathfrak{b}')$ is defined in particular when the support of $\mathfrak{b} \times \mathfrak{b}'$ misses that of
$\mathcal{P}$): $\eta = d\mathfrak{a} \cup \mathfrak{a}' - \mathfrak{a} \cup d\mathfrak{a}' = d\epsilon$, local lifts $b_v$ of
points $\beta_v$ with $\alpha_v = d\beta_v$,

$$\gamma_v = (\mathfrak{a}_v - db_v) \cup \mathfrak{a}'_v - b_v \cup d\mathfrak{a}'_v - \epsilon_v,$$

and $\langle a, a'\rangle_{\mathcal{P}} = \sum_v \mathrm{inv}_v(c_v)$ for the classes $c_v$ of the cocycles $\gamma_v$. The value does not depend
on the choices.

Poonen and Stoll define $\langle\,,\rangle_D$ for any divisor $D$ on a product $V \times W$ of geometrically integral,
smooth, projective varieties; this is the case
$V = A$, $W = A^\vee$ and $D = \mathcal{P}$.

## Expansion

This node is still to be broken down. A good expansion states and links:

- the cocycle conditions, as for the
  [Albanese–Picard definition](albanese-picard-definition-of-the-cassels-tate-pairing.md), with
  [Lang's reciprocity law](../construction-of-the-cassels-tate-pairing/lang-reciprocity-law.md) for the agreement of the two
  pairings on $Y^0 \times Y^0$;
- the independence of the choices, the choice of $\beta_v$ through the local triviality of $a'$ and the choice of $\epsilon$
  through the vanishing of the sum of the local invariants of a global class.

## Depends on

- [The Weil pairing through a Poincaré divisor](../construction-of-the-cassels-tate-pairing/weil-pairing-through-a-poincare-divisor.md), for Poincaré divisors and the values $\mathcal{P}(\mathfrak{b}, \mathfrak{b}')$
- [The Albanese–Picard definition of the Cassels–Tate pairing](albanese-picard-definition-of-the-cassels-tate-pairing.md), whose steps the definition follows
- [Selmer groups and the torsion of the Shafarevich–Tate group of an abelian variety](../selmer-groups-of-abelian-varieties.md), for $\text{Ш}(K, A)$ and $\text{Ш}(K, A^\vee)$
- [Vanishing of the third cohomology of the multiplicative group of a number field](../../../algebraic-number-theory/galois-representations/galois-cohomology-of-number-fields/vanishing-of-h3-of-the-multiplicative-group.md), for $\epsilon$
- [Local class field theory: cohomology and the existence theorem](../../../p-adic-numbers/local-class-field-theory-cohomology.md), for the local invariant maps (its item 2)
- [Cohomology of profinite groups](../../../../RepresentationTheory/group-cohomology/cohomology-of-profinite-groups.md), for cochains and their cup products

## Proof depends on

- [Lang's reciprocity law for divisors on a product](../construction-of-the-cassels-tate-pairing/lang-reciprocity-law.md)
- [The local invariants of a global class in H² sum to zero](../../../algebraic-number-theory/adeles-class-field-theory/reciprocity-law/sum-of-local-invariants.md)

## Sources

- B. Poonen and M. Stoll, *The Cassels-Tate pairing on polarized abelian varieties*, Ann. of Math. (2) 150 (1999),
  1109–1149, doi:10.2307/121064: §12.1, "The Albanese-Albanese definition", p. 1143 ("One can simply mimic the
  construction in Section 3.2", the pairings "that agree on $\mathcal{Y}^0(V_{k^{\mathrm{sep}}}) \times \mathcal{Y}^0(W_{k^{\mathrm{sep}}})$ by
  Lang reciprocity"); §12, p. 1142 (the choices are made so that the pairings are defined).
