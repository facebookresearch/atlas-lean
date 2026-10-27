---
article_id: af_d2a3869b4302dfec3cca71f5
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.young_reverse_multiple_carry_path_iff_general
---

# Young reverse multiple carry path iff general

Carry recurrence for reverse multiples, with only the hypotheses the
argument uses: for `2 ≤ k < g` and little-endian base-`g` digits `a`, `k` times the number equals
its digit reversal exactly when there is a unique carry sequence `r` with `r 0 = 0`, `r n = 0`,
every carry below `k`, and the column equations. The digit length may be `0` and the end digits
may vanish. `young_reverse_multiple_carry_path_iff` is the source-shaped form.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.NumberTheory.Digits.YoungReverseMultipleCarryPath](../../../../../../sources/v2/MathlibExt.md)
