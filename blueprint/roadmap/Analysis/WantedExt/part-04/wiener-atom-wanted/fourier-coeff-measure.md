---
article_id: af_99741048eec49105d3b62b26
declaration: def
origin: cited
statement: formalized
lean: MathlibExt.Analysis.WienerAtomWanted.Analysis.fourierCoeffMeasure
---

# Fourier Coeff Measure

The `k`-th Fourier coefficient of a Borel measure `μ` on the circle
`AddCircle (2π)`: `μ̂_k := ∫ exp(i k x) dμ(x)`. With mathlib's normalisation
`fourier k x = exp(2π i k x / T)`, taking `T = 2π` gives `exp(i k x)`.

## Depends on

This node has no prerequisites.

## Sources

- [WantedExt, WantedExt.Analysis.WienerAtomWanted](../../../../../sources/v2/WantedExt.md)
