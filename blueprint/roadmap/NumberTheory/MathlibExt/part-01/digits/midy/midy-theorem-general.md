---
article_id: af_06420dd87cb144e40e78a439
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.midy_theorem_general
---

# Midy theorem general

Midy's theorem with only the hypotheses the argument uses: if a prime `p` divides
`10 ^ (2 * n) - 1` but not `10 ^ n - 1`, the two `n`-digit halves of `(10 ^ (2 * n) - 1) / p`
sum to `10 ^ n - 1`. `midy_theorem` is the source-shaped form, which assumes the repetend period
of `1 / p` is exactly `2 * n`.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.NumberTheory.Digits.Midy](../../../../../../sources/v2/MathlibExt.md)
