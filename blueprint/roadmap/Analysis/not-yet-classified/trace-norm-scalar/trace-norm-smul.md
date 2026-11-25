# Trace Norm smul

Complex scalar multiplication scales trace norm by the scalar absolute value, including a zero
scalar.

Here `n` is any finite index type with decidable equality. The matrices are arbitrary square
complex matrices, and the empty-index case is included.

```lean
theorem singularValueTraceNorm_smul (c : ℂ) (M : Matrix n n ℂ) :
    (c • M).singularValueTraceNorm = ‖c‖ * M.singularValueTraceNorm
```
