---
article_id: af_aee15d1f9dc0762e11b3e095
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.catalan_odd_iff
---

# Catalan Parity

Catalan parity characterization: `catalan n` is odd if and only if `n` is one
less than a power of two, i.e. `∃ a : ℕ, n = 2 ^ a - 1`.

Authoritative source: Alon Regev, "The Central Component of a Triangulation",
Journal of Integer Sequences 16 (2013), Article 13.4.1, theorem `oddcats`,
lines 132–147 of <https://cs.uwaterloo.ca/journals/JIS/VOL16/Regev/regev4.tex>.
This entry records the displayed theorem statement. Lines 85–88 define `C_n`
with the standard indexing used by Mathlib's `catalan`, so no index shift is
required. The natural subtraction in `2 ^ a - 1` is safe because `2 ^ a` is
positive. No parallel Catalan definition is introduced.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.Combinatorics.Enumerative.CatalanParity](../../../../../../sources/v2/MathlibExt.md)
