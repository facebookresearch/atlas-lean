---
article_id: af_088119369d7202f533639c91
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.von_szily_super_catalan_identity
---

# Von Szily Super Catalan

Von Szily identity for the super Catalan numbers `S(m, n)`: the source
normalization `(2 * m)! * (2 * n)! / (m! * n! * (m + n)!)` equals the
all-integer alternating sum with plus-plus indices `choose (2 * m) (m + k)`
and `choose (2 * n) (n + k)`, summed over exactly its simultaneous finite
binomial support.

Math notes: the source sums over `k ∈ ℤ`; only finitely many terms are
nonzero, represented here by the `Finset.Icc` of the common support.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.Combinatorics.VonSzilySuperCatalan](../../../../sources/v2/MathlibExt.md)
- Kendra Killpatrick, *Super FiboCatalan Numbers and Their Lucas Analogues*, Journal of Integer Sequences 28 (2025), Article 25.5.8, von Szily identity quoted in the Open problems section, lines 671–674, <https://cs.uwaterloo.ca/journals/JIS/VOL28/Killpatrick/killp6.tex>, citing I. Gessel, *Super ballot numbers*, J. Symbolic Comput. 14 (1992), p. 11.
