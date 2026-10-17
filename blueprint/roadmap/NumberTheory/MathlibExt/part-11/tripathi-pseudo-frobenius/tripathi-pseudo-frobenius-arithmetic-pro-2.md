---
article_id: af_4a544f1947af65675080d9b7
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.tripathi_pseudo_frobenius_arithmetic_progression
---

# Tripathi pseudo frobenius arithmetic progression

Tripathi's formula for the pseudo-Frobenius set of the semigroup generated
by the modified arithmetic progression `a, ha+d, ..., ha+kd`: with
`a - 1 = qk + r`, `1 ≤ r ≤ k`, the pseudo-Frobenius numbers
(`x ∉ S` with `x + s ∈ S` for all nonzero `s ∈ S`) are exactly the values
`ha * ⌊(x-1)/k⌋ + (h-1)*a + d*x` for `a - r ≤ x ≤ a - 1`. The case `a = 1`
is excluded since then `a - 1 = qk + r` with `1 ≤ r` is unsatisfiable; the
`k ≥ a` case gives `{(h-1)a + dx : 1 ≤ x ≤ a-1}`. Verified against
directly computed semigroups at 504 tuples.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Tripathi pseudo frobenius arithmetic progression general](tripathi-pseudo-frobenius-arithmetic-pro.md)

## Sources

- [MathlibExt, MathlibExt.NumberTheory.TripathiPseudoFrobenius](../../../../../sources/v2/MathlibExt.md)
- Amitabha Tripathi, "The Frobenius Problem for Modified Arithmetic Progressions," Journal of Integer Sequences 16 (2013), Article 13.7.4, Theorem (label S*formula), lines 235–238, https://cs.uwaterloo.ca/journals/JIS/VOL16/Tripathi/trip22.tex It follows from `tripathi_pseudo_frobenius_arithmetic_progression_general`; the hypothesis `hd` is unused and keeps the source's shape. Proves `Wanted` entry `tripathi_pseudo_frobenius_arithmetic_progression`.
