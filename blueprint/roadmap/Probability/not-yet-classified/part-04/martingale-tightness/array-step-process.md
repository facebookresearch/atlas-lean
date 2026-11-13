# Array Step Process

The **step process** of a triangular array in `D([0,1])`: row `n` uses the increments
`ξ n 0, …, ξ n (n-1)` placed at times `1/n, …, 1`, so the path is
`t ↦ ∑_{i < ⌊n t⌋} ξ n i` (`arrayStepProcess_apply`). It is T43's `skorokhodStepProcess` with
the `1/√n` normalization undone, because an array row carries its own scaling.
