---
article_id: af_d7f233cb6ac7fdca724f4e0e
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.fraenkel_exact_M_cover_bernoulli_recurrence
---

# Fraenkel exact M cover bernoulli recurrence

Fraenkel exact `M`-cover Bernoulli recurrence (normalized indexed form).

Uses the source convention `B₁ = -1/2`, matching Mathlib's `bernoulli : ℕ → ℚ`
from `Mathlib.NumberTheory.Bernoulli`. The auxiliary polynomial
`bhat_m(t) = ∑_{s=0}^{m-1} B_s * choose(m,s) * t^(m-s)` is inlined as the
`Finset.range m` sum on the right-hand side.

The normalized indexed exact `M`-cover hypotheses are `q ≥ 2`, `m ≥ 1`,
`n i > 0`, `a i < n i`, with repeated residue classes preserved by indexing
with `Fin q`. The exact-cover hypothesis is encoded with the repository API
`Int.indexedCoverMultiplicity` (moduli `n`, residues `(a i : ℤ)`), asserting
multiplicity `M` for every `k : ℤ`.

Scope: this file states only equation (23) in the direction above. It does not
add the iff converse, the Beebee `x`-parameter variant, or the Porubsky
weighted variant.

## Depends on

- [Indexed Cover Multiplicity](../../part-01/covering-system/exact-cover/indexed-cover-multiplicity.md)

## Proof depends on

- [Fraenkel exact M cover bernoulli recurrence general](fraenkel-exact-m-cover-bernoulli-recurre.md)

## Sources

- [MathlibExt, MathlibExt.NumberTheory.FraenkelCoveringBernoulli](../../../../../sources/v2/MathlibExt.md)
- Yevgenya Movshovich, "Raabe's Identity and Covering Systems," Journal of Integer Sequences 23 (2020), Article 20.2.8, <https://cs.uwaterloo.ca/journals/JIS/VOL23/Movshovich/movsho5.tex>. Equation (23); exact source span: lines 228–241; full live TeX source-file SHA-256 `24b31e07198371d27b492f46b2d747aa49e9a49323696d6b4a9c18deab8ff593`; exact newline-terminated equation/context span SHA-256 `1c95008be9bbbc150a494df7eef936abd3ee277ab9bd32ff1f67b0b0f4b76526`.
