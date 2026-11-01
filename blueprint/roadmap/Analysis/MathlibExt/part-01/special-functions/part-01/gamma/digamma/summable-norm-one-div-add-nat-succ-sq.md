---
article_id: af_af56afd3469f5f362239eaf8
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Complex.summable_norm_one_div_add_nat_succ_sq
---

# Summable norm one div add nat succ sq

The trigamma series `∑ 1 / (z + k + 1)²` converges absolutely for every `z : ℂ`.
At a pole `z = -(k + 1)` Lean's totalized division makes that term `0`, so no
pole-avoidance hypothesis is needed.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.Analysis.SpecialFunctions.Gamma.Digamma](../../../../../../../../sources/v2/MathlibExt.md)
