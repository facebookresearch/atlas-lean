# Toroidal compactifications of unitary Shimura varieties

This node is still to be broken down. It covers the toroidal compactifications of moduli spaces of
abelian schemes with an action of the ring of integers of a CM field, of unitary signature $(p, q)$,
in the form that Alpöge's library uses, with charts given by a fan and the logarithmic Kodaira–Spencer
isomorphism; the Siegel case is outlined in the node on [moduli of principally polarized abelian
varieties](moduli-of-principally-polarized-abelian-varieties.md). The targets are the following, for a
CM field $E$, a unitary datum of signature $(p, q)$ with $p + q \ge 1$, a level and the moduli scheme
$X^\circ$ attached to them, over the coefficient field of the datum.

1. (Compactification.) There is a toroidal model $Y$ of $X^\circ$, smooth of the expected relative
   dimension, whose boundary is a divisor with simple normal crossings, and over whose interior the
   logarithmic Kodaira–Spencer map of the universal family is an isomorphism.
2. (Charts for a fan.) For a polarized fan $\varphi$ without self-intersections, there are such a model
   $Y$, an effective Cartier divisor $B$ supported outside the abelian locus, and integers $d, k \ge 1$
   such that $Y$ has charts given by $\varphi$ at every boundary point, controlled by $B$ and $d$, and,
   when the determinant of the sheaf of logarithmic differentials is invertible, the line bundle built
   from it, $k$ and $B$ is ample.

A good expansion has pages for the moduli problems of PEL type attached to unitary groups and their
integral models; their toroidal compactifications attached to smooth projective cone decompositions,
with simple normal crossing boundary and log Kodaira–Spencer isomorphism (Lan's theory of PEL-type
compactifications, of which Lan's Theorem 6.1 is a projective form; Madapusi Pera, Theorem 2, for
Hodge type); and the comparison of their charts with toric charts given by a fan without
self-intersections.

## Depends on

- [Moduli of principally polarized abelian varieties and their compactifications](moduli-of-principally-polarized-abelian-varieties.md)

## Sources

- K.-W. Lan, "Integral models of toroidal compactifications with projective cone decompositions",
  <https://www.kwlan.org/articles/cpt-ram-nbl.pdf>: Definitions 2.1–2.2 and Theorem 6.1 (PEL type).
- K. Madapusi Pera, "Toroidal compactifications of integral models of Shimura varieties of Hodge
  type", arXiv:1211.1731: introduction, Theorem 2.
- Provenance: Alpöge's Lean library (<https://alpo.ge/remark.pdf>; source mirror
  <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>) states 1 as `GlobalTheory.Published.ToroidalCompactification` and 2 as
  `GlobalTheory.Published.ToroidalForFanKS`, with its own definitions of the data, charts and fans; no
  published source stating them in this form has been identified.
