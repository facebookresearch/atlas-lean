# Toroidal compactifications of unitary Shimura varieties

This node is still to be broken down. It covers the toroidal compactifications of moduli spaces of
abelian schemes with an action of the ring of integers of a CM field, of unitary signature $(p, q)$,
in the form that Alpöge's library uses, with charts given by a fan and the logarithmic
Kodaira–Spencer isomorphism on the whole compactification; the Siegel case is outlined in the node
on
[moduli of principally polarized abelian varieties](moduli-of-principally-polarized-abelian-varieties.md).
The targets are the following, for a CM field $E$, a unitary datum of signature $(p, q)$ with $p + q
\ge 1$, a level and the moduli scheme $X^\circ$ attached to them, over the coefficient field $F$ of
the datum. Write $G$ for the semi-abelian scheme over a toroidal model $Y$ extending the universal
family, $Y^\circ \subset Y$ for the interior and $\mathcal{J}$ for the ideal sheaf of the boundary
$Y \setminus Y^\circ$.

1. (Compactification.) There is a toroidal model $Y$ of $X^\circ$ over $F$, smooth of the expected
   relative dimension, whose boundary is a divisor with simple normal crossings, with the
   logarithmic Kodaira–Spencer isomorphism **on every affine open $U$ of $Y$**, boundary points
   included: for a frame $v_1, \dots, v_n$ of the tangent space of $G$ along the zero section over
   $U$, with the matrices of the action of $\mathcal{O}_E$ in this frame, there is an isomorphism
   from the module of logarithmic derivations of $U$ over $F$ along $\mathcal{J}$ onto the module of
   matrices balanced for that action, under which the Kodaira–Spencer matrix of a logarithmic
   derivation is its image. Over $Y^\circ$ this is the ordinary Kodaira–Spencer isomorphism; its
   extension over the boundary is part of the target, not a consequence of the interior statement.
2. (Charts for a fan.) For a polarized fan $\varphi$ without self-intersections, there are such a
   model $Y$, an effective Cartier divisor $B$ on $Y$ whose support misses the abelian locus, and
   integers $d, k \ge 1$ such that: the generic fibre is smooth of the expected dimension with
   simple normal crossing boundary; at every boundary point there is a chart for $\varphi$ (an étale
   completion $\operatorname{Spec} k[[\dots]]$ with boundary parameters whose product cuts out the
   boundary, a uniformization of the pull-back of $G$ whose period forms are the level multiples of
   forms $\delta_i$ in a cone of $\varphi$, and $B$ cut out by $\prod_i t_i^{a_i}$ with $a_i = d\,
   \varphi(\gamma_i)$); writing $\omega_Y = (\det \operatorname{Lie} G)^\vee$ for the Hodge line
   bundle, the line bundle $\omega_Y^{\otimes k} \otimes \mathcal{O}_Y(-B)$ is ample whenever
   $\omega_Y$ is invertible; and the logarithmic Kodaira–Spencer isomorphism of 1 holds on $Y$.

In Alpöge's library 1 is deduced from 2: the target of the node on the
[Hodge bundle on toroidal compactifications of Siegel moduli schemes](hodge-bundle-on-siegel-toroidal-compactifications.md)
(`SiegelToroidalIntegral`) supplies a polarized fan without self-intersections, to which 2 applies
(`exists_model` in `PublishedTheorems/Divisors₂/ToroidalCompactificationBis.lean`).

The hypotheses of the classical constructions are different from these data: Lan constructs toroidal
compactifications of PEL type for a neat level and a smooth projective compatible collection of cone
decompositions (Definitions 2.1–2.2, Remark 2.3, Theorem 6.1), and Madapusi Pera, for Hodge type,
for a good local level and a smooth admissible cone decomposition (Theorem 2). Neither source states
the logarithmic Kodaira–Spencer isomorphism on all of $Y$ in the form of 1, the charts of 2 for the
fan $\varphi$, or the ampleness of the twist of 2. A good expansion has pages for the moduli
problems of PEL type attached to unitary groups and their integral models; their toroidal
compactifications for smooth projective cone decompositions; the logarithmic Kodaira–Spencer
isomorphism on the compactification; the comparison of their charts with toric charts given by a fan
without self-intersections; and the ampleness of $\omega_Y^{\otimes k} \otimes \mathcal{O}_Y(-B)$.

## Depends on

- [Moduli of principally polarized abelian varieties and their compactifications](moduli-of-principally-polarized-abelian-varieties.md)
- [Simple normal crossing divisor](../../birational-geometry/simple-normal-crossing-divisor.md), for
  the boundary with simple normal crossings over the characteristic-zero field $F$, in 1 and 2

## Proof depends on

- [Hodge bundle on toroidal compactifications of Siegel moduli schemes](hodge-bundle-on-siegel-toroidal-compactifications.md),
  for the polarized fan of its target, from which Alpöge's library deduces 1 from 2

## Sources

- K.-W. Lan, "Integral models of toroidal compactifications with projective cone decompositions",
  <https://www.kwlan.org/articles/cpt-ram-nbl.pdf>: Definitions 2.1–2.2, Remark 2.3 and Theorem 6.1
  (PEL type).
- K. Madapusi Pera, "Toroidal compactifications of integral models of Shimura varieties of Hodge
  type", arXiv:1211.1731: introduction, Theorem 2.
- Provenance: Alpöge's Lean library (<https://alpo.ge/remark.pdf>; source mirror
  <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>)
  states 1 as `GlobalTheory.Published.ToroidalCompactification` and 2 as
  `GlobalTheory.Published.ToroidalForFanKS`, with its own definitions of the data, the fan
  conditions `IsPolFan` and `NoSelfInt`, the charts `HasChartOf`, the Hodge line bundle
  `FlagMod.detOm` (the dual of the determinant of the Lie algebra of $G$), the twist `TorRef.polOf`
  and the logarithmic Kodaira–Spencer condition `HasLogKS`, which quantifies over every affine open
  of $Y$; no published source stating them in this form has been identified.
