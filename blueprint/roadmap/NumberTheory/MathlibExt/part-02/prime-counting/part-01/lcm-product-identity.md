---
article_id: af_7208266c6dd679c828024d7b
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.lcm_product_identity
---

# Lcm Product Identity

The LCM product identity: `∏_p p^⌊n/(p-1)⌋` equals the lcm of all products
`i_1 * ... * i_n` of positive integers with sum at most `2 * n`.

The source's product ranges over all primes, but `⌊n/(p-1)⌋ = 0` for
`p > n + 1`, so `Nat.primesBelow (n + 2)` captures every nontrivial factor.
The tuple ranges over `Fin (2 * n + 1)` with the `1 ≤` filter selecting the
positive entries; verified at `n = 0, 1, 2, 3` against directly computed lcms.
Proves `Wanted` entry `lcm_product_identity`.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.NumberTheory.PrimeCounting.LcmProductIdentity](../../../../../../sources/v2/MathlibExt.md)
- Abdelmalek Bedhouche and Bakir Farhi, "On Some Products Taken over Prime Numbers," Journal of Integer Sequences 26 (2023), Article 23.1.5, Corollary (label coll2), lines 335–340, https://cs.uwaterloo.ca/journals/JIS/VOL26/Farhi/farhi32.tex
