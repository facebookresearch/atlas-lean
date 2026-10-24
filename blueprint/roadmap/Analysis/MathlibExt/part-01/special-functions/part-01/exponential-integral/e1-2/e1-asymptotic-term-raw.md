---
article_id: af_63da65d0b9cf9fcf3fc87a5f
declaration: def
origin: cited
statement: formalized
lean: Complex.e1AsymptoticTermRaw
---

# E1 Asymptotic Term Raw

Totalized `n`-th asymptotic-expansion term.

At `z = 0` the divisions by zero evaluate to junk (`x / 0 = 0`), hence the
term is `0`, with no classical meaning. Use `e1AsymptoticTerm` with a `z ≠ 0`
proof for the domain-safe API.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.Analysis.SpecialFunctions.ExponentialIntegral.E1](../../../../../../../../sources/v2/MathlibExt.md)
