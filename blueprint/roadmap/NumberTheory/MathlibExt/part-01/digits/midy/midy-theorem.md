---
article_id: af_703e2ad071c2c5dcb30459f2
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.midy_theorem
---

# Midy theorem

Midy's theorem (https://en.wikipedia.org/wiki/Midy%27s_theorem, statement `midy-s1`):
a prime `p ≠ 2, 5` whose repetend period of `1 / p` in base 10 is even, `2 * n`,
splits into two `n`-digit halves summing to `10 ^ n - 1`.
It follows from `midy_theorem_general`, which needs `hmin` only at `m = n`; the hypotheses
`h2` and `h5` are unused and keep the source's shape.
Proves `Wanted` entry `midy_theorem`.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Midy theorem general](midy-theorem-general.md)

## Sources

- [MathlibExt, MathlibExt.NumberTheory.Digits.Midy](../../../../../../sources/v2/MathlibExt.md)
