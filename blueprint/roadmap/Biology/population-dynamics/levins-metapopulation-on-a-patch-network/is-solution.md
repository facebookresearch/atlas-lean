# Solution of the Levins system on a patch network

For a finite set `ι` of patches, a real matrix `C` and real rates `e`, a function `p : ℝ → ℝ^ι` is a
solution if for every `t ≥ 0` it has derivative `p'(t) = F(p(t))`, where `F` is the
[vector field](field.md). At `t = 0` the derivative is two-sided; nothing else is required for
`t < 0`.
