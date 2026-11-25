# Trace Norm smul sub

Scaling both matrices in a difference scales its trace norm by the complex scalar absolute
value.

Here `n` is any finite index type with decidable equality. The matrices are arbitrary square
complex matrices, and the empty-index case is included.

```lean
theorem traceNorm_smul_sub (c : ℂ) (M N : Matrix n n ℂ) :
    (c • M - c • N).traceNorm = ‖c‖ * (M - N).traceNorm
```
