# The Albanese–Picard definition of the Cassels–Tate pairing

Let $K$ be a number field, $A$ an [abelian variety](../../../../AlgebraicGeometry/abelian-varieties/abelian-scheme.md) over
$K$ with [dual](../../../../AlgebraicGeometry/abelian-varieties/dual-abelian-variety.md) $A^\vee$, and $V$ either $A$ or a
principal homogeneous space $X$ of $A$ over $K$, with the exact sequences and the pairings $\cup$ (the
[Albanese–Picard pairing](albanese-picard-pairing-of-zero-cycles-and-divisors.md) on $Y^0 \times \operatorname{Div}^0$ and
evaluation on $Z^0 \times \bar K(V)^\times/\bar K^\times$) of $V$ over $K$ and over each completion $K_v$, the group law of $\bar K^\times$
written additively. For $a \in \text{Ш}(K, A)$ and $a' \in \text{Ш}(K, A^\vee)$ define $\langle a, a'\rangle_V \in \mathbb{Q}/\mathbb{Z}$ as follows.

1. Choose cocycles $\alpha \in Z^1(G_K, A(\bar K))$ and $\alpha' \in Z^1(G_K, A^\vee(\bar K))$ representing $a$ and $a'$, and lift them
   to cochains $\mathfrak{a} \in C^1(G_K, Z^0(V_{\bar K}))$ and $\mathfrak{a}' \in C^1(G_K, \operatorname{Div}^0(V_{\bar K}))$ such that all
   $G_K$-conjugates of $\mathfrak{a}_\sigma$ have support disjoint from that of $\mathfrak{a}'_\tau$, for all $\sigma, \tau \in G_K$.
2. Then $\eta = d\mathfrak{a} \cup \mathfrak{a}' - \mathfrak{a} \cup d\mathfrak{a}' \in C^3(G_K, \bar K^\times)$ is a cocycle, and as
   $H^3(G_K, \bar K^\times) = 0$, $\eta = d\epsilon$ for some $\epsilon \in C^2(G_K, \bar K^\times)$.
3. For each place $v$ choose $\beta_v \in A(\bar K_v)$ with $\alpha_v = d\beta_v$, and $b_v \in Z^0(V_{\bar K_v})$ mapping to $\beta_v$ such
   that all $G_v$-conjugates of $b_v$ have support disjoint from that of $\mathfrak{a}'_\sigma$, for all $\sigma \in G_K$. Then

    $$\gamma_v = (\mathfrak{a}_v - db_v) \cup \mathfrak{a}'_v - b_v \cup d\mathfrak{a}'_v - \epsilon_v \in C^2(G_v, \bar K_v^\times)$$

    is a cocycle, representing $c_v \in \mathrm{Br}(K_v)$; here $\mathfrak{a}_v - db_v$ takes values in $Y^0$, and the term
    cannot be split.
4. $\langle a, a'\rangle_V = \sum_v \mathrm{inv}_v(c_v)$.

The value is defined and does not depend on the choices; the independence of $\beta_v$ uses the local triviality of $a'$.

## Expansion

This node is still to be broken down. A good expansion states and links:

- that the choices with the required supports exist (Poonen and Stoll, §12, p. 1142: "It is not difficult to see that this
  is always possible");
- the cocycle conditions, from $d(x \cup y) = dx \cup y + (-1)^{\deg x} x \cup dy$ and the agreement of the two pairings on
  $Y^0 \times \bar K(V)^\times/\bar K^\times$;
- the vanishing of $c_v$ for all but finitely many $v$, and the independence of all choices, the choice of $\beta_v$ through the
  local triviality of $a'$, and the choice of $\epsilon$ through
  [the vanishing of the sum of the local invariants of a global class](../../../algebraic-number-theory/adeles-class-field-theory/reciprocity-law/sum-of-local-invariants.md).

## Depends on

- [The Albanese–Picard pairing of zero-cycles and divisors](albanese-picard-pairing-of-zero-cycles-and-divisors.md)
- [Selmer groups and the torsion of the Shafarevich–Tate group of an abelian variety](../selmer-groups-of-abelian-varieties.md), for $\text{Ш}(K, A)$ and $\text{Ш}(K, A^\vee)$
- [Vanishing of the third cohomology of the multiplicative group of a number field](../../../algebraic-number-theory/galois-representations/galois-cohomology-of-number-fields/vanishing-of-h3-of-the-multiplicative-group.md), for $\epsilon$
- [Local class field theory: cohomology and the existence theorem](../../../p-adic-numbers/local-class-field-theory-cohomology.md), for the local invariant maps (its item 2)
- [Cohomology of profinite groups](../../../../RepresentationTheory/group-cohomology/cohomology-of-profinite-groups.md), for cochains and their cup products

## Proof depends on

- [The local invariants of a global class in H² sum to zero](../../../algebraic-number-theory/adeles-class-field-theory/reciprocity-law/sum-of-local-invariants.md)

## Sources

- B. Poonen and M. Stoll, *The Cassels-Tate pairing on polarized abelian varieties*, Ann. of Math. (2) 150 (1999),
  1109–1149, doi:10.2307/121064: §3.2, pp. 1116–1117 (the definition (1) for any variety $V$, with
  $\text{Ш}(\mathrm{Alb}^0_{V/k}) \times \text{Ш}(\mathrm{Pic}^0_{V/k,\mathrm{red}}) \to \mathbb{Q}/\mathbb{Z}$, and footnote 6; "One checks using
  $d(x \cup y) = dx \cup y + (-1)^{\deg x} x \cup dy$ [AW, p. 106] that this is well-defined and independent of choices. In
  proving independence of the choice of $\beta_v$ one uses the local triviality of $a'$, which has not been used so far").
