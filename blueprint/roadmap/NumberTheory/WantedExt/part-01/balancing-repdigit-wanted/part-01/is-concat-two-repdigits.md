---
declaration: def
origin: cited
statement: formalized
lean: MetaMathlibExt.IsConcatTwoRepdigits
---

# Is Concat Two Repdigits

Concatenation of two repdigits (in the strict sense of Integers 2025,
A15): the decimal expansion of `n` consists of a block of `m₁ ≥ 1` digits
`d₁ ∈ [1, 9]` followed by a block of `m₂ ≥ 1` digits `d₂ ∈ [0, 9]` with
`d₁ ≠ d₂`, i.e. the expansion has exactly two digit runs.

The distinctness condition is required by the paper's classifications: for
example `C_4 = 99` is not listed in its Lemma 5.

## Depends on

This node has no prerequisites.

## Sources

- [WantedExt, WantedExt.NumberTheory.BalancingRepdigitWanted](../../../../../../sources/v2/WantedExt.md)
- Mohapatra, Bhoi and Panda, *Balancing and Lucas-Balancing Numbers as the Difference of Two Repdigits*, INTEGERS 25 (2025), Article A15, Lemmas 3 and 5.
