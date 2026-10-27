---
article_id: af_9535b720f2981f470f3262b7
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.boxProd_tiling_card_eq_fib_mul_pellNumber
---

# Box Prod tiling card eq fib mul pell Number

The number of domino tilings, as perfect matchings, of `W_4 □ P_{n-1}`
equals `Nat.fib n * pellNumber n` for `n ≥ 2`, with the Pell factor stated via
the canonical `MetaMathlibExt.pellNumber` sequence.

This is the `pellNumber` form of `boxProd_tiling_card_eq_fib_mul_pell`, which
keeps the inline `Nat.rec` spelling of the Pell factor for the `Wanted` entry.

## Depends on

- [Pell Number Sequence](../../../../../../NumberTheory/MathlibExt/part-08/pell-number.md)

## Sources

- [MathlibExt, MathlibExt.Combinatorics.Enumerative.W4PathDominoTilings](../../../../../../../sources/v2/MathlibExt.md)
