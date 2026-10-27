---
article_id: af_b4e74ba7f9dfef6615c00f9a
declaration: def
origin: cited
statement: formalized
lean: MetaMathlibExt.mathieuFibonacciFourierCoefficient
---

# Mathieu Fibonacci Fourier Coefficient

Fourier cosine-series coefficient from the periodic Mathieu–Fibonacci example.

For `n ≥ 1`, this is `(2 / Real.log ((1 + Real.sqrt 5) / 2)) *
‖Complex.Gamma (1 + 2 * n * π * I / Real.log ((1 + Real.sqrt 5) / 2))‖ ^ 2`,
where `Real.log ((1 + Real.sqrt 5) / 2)` is the fixed `log φ` of the source,
so that the source periodic function is
`H x = 1 + ∑' n : {n : ℕ // 1 ≤ n}, coeff n * Real.cos (4 * n * π * x / log φ)`.

Concept `Fourier series coefficient` (`jis_sem_e469cc9709bc61c7d3368fdf`);
required clause from statement `jis_730fbe152ebd86322427d06f`.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.Analysis.SpecialFunctions.MathieuFibonacciFourierCoefficient](../../../../../../sources/v2/MathlibExt.md)
