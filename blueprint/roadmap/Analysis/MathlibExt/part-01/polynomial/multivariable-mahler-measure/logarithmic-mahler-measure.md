---
article_id: af_c18dee63b94fa971eb8dc1ff
declaration: def
origin: cited
statement: formalized
lean: LogarithmicMahlerMeasure.logarithmicMahlerMeasure
---

# Logarithmic Mahler Measure

The multivariable logarithmic Mahler measure of a complex Laurent polynomial.

The cited source applies this formula to nonzero polynomials. Following Mathlib's
`Polynomial.logMahlerMeasure`, the Lean definition is total; in particular, its value at zero is
zero under `Real.log_zero` and the convention for the Bochner integral.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Normalized Box Integral](normalized-box-integral.md)
- [Torus Eval](torus-eval.md)

## Sources

- [MathlibExt, MathlibExt.Analysis.Polynomial.MultivariableMahlerMeasure](../../../../../../sources/v2/MathlibExt.md)
