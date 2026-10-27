---
article_id: af_3e0865b0c1b0952bb951d819
declaration: abbrev
origin: cited
statement: formalized
lean: Real.LogarithmicIntegralDomain
---

# Logarithmic Integral Domain

Domain of the normalized logarithmic integral: `0 ≤ x` and `x ≠ 1`.

`1` is excluded because `1 / log t` is singular at `t = 1`; the classical
integral `∫₀ˣ dt / log t` has no finite real value at `x = 1` and is
understood as a Cauchy principal value for `x ≠ 1`.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.Analysis.SpecialFunctions.Log.Integral](../../../../../../../../sources/v2/MathlibExt.md)
- arXiv:2306.14073v1 and arXiv:2309.16007v1, classical `li(x) := PV ∫₀ˣ dt/log t` with lower limit `0` and principal value at `t = 1`.
