---
article_id: af_4d59638c0f17dd1e038dcba8
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.cipolla_pseudoprime_construction
---

# Cipolla Pseudoprime

Cipolla construction of a pseudoprime to base `a`: for prime `p` not
dividing `a * (a^2 - 1)`, `n = n₁ * n₂` with `n₁ = (a^p - 1)/(a - 1)` and
`n₂ = (a^p + 1)/(a + 1)` is composite with `a^(n-1) ≡ 1 [MOD n]`.

Pinned Mathlib already contains this construction internally; this theorem
exposes it publicly through `Nat.FermatPsp`.
Proves `Wanted` entry `cipolla_pseudoprime_construction`.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.NumberTheory.CipollaPseudoprime](../../../../sources/v2/MathlibExt.md)
- Y. Hamahata and Y. Kokubun, "Cipolla Pseudoprimes", Journal of Integer Sequences 10 (2007), Theorem 1 (Cipolla, cf. Ribenboim), lines 87--95, <https://cs.uwaterloo.ca/journals/JIS/VOL10/Hamahata2/hamahata44.tex>.
