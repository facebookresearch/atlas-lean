# Good hermitian metrics and Chern numbers

This node is still to be broken down. It covers Mumford's theory of good singular hermitian metrics on
vector bundles over the complement of a normal crossing divisor, used for Hirzebruch's proportionality
on non-compact quotients of bounded symmetric domains such as the moduli spaces of polarized
[abelian varieties](moduli-of-principally-polarized-abelian-varieties.md). Let $\bar X$ be a smooth
projective complex variety, $D \subset \bar X$ a divisor with normal crossings, $X = \bar X \setminus
D$, and $\bar E$ a vector bundle on $\bar X$ with a hermitian metric $h$ on $E|_X$. The targets are:

1. (Good metrics.) The notion of a good metric $h$: near $D$, $h$ and its inverse grow at most
   logarithmically, and the connection and curvature forms satisfy Poincaré growth estimates. For a
   good metric the Chern forms of $(E|_X, h)$ are locally integrable on $\bar X$, define closed currents,
   and represent the Chern classes of $\bar E$; in particular Chern numbers of $\bar E$ are integrals over
   $X$ of polynomials in the Chern forms of $h$ (Mumford, Theorem 1.4).
2. (Flag push-forward.) The identity, for a vector bundle with a filtration and its flag bundle,
   between intersection numbers on the flag variety and polynomials in the Chern classes of the bundle,
   through the discriminant of the Chern roots, in characteristic zero.
3. (Proportionality.) Hirzebruch–Mumford proportionality for the automorphic vector bundles on a
   smooth toroidal compactification of an arithmetic quotient of a bounded symmetric domain (Mumford,
   §3).

A good expansion has pages for: good forms and good metrics, and Mumford's Theorem 1.4 that Chern forms
of good metrics compute the Chern classes of the extension (Mumford, §1); the canonical extensions of
automorphic vector bundles to toroidal compactifications with their good invariant metrics (Mumford,
§§2–3); and the splitting principle and flag bundles for 2.

## Depends on

- [Moduli of principally polarized abelian varieties and their compactifications](moduli-of-principally-polarized-abelian-varieties.md)

## Sources

- D. Mumford, "Hirzebruch's proportionality theorem in the non-compact case", Invent. Math. 42
  (1977), 239–272.
- Provenance: Alpöge's Lean library (<https://alpo.ge/remark.pdf>; source mirror
  <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>) states 1 and 2, with its own definitions of good metrics, flags and Chern
  integrals, as `GlobalTheory.Published.GoodChernWeil` (the conjunction of `GoodChernNumbers` and
  `FlagPushForward`), and a proportionality statement for unitary Shimura varieties as
  `GlobalTheory.Published.MumfordProportionality`.
