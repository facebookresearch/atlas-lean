# In a mass-orthonormal modal basis, Rayleigh damping is diagonal

Let `n` be a finite set, `M`, `K` and `Φ` real `n × n` matrices and `μ : n → ℝ` with
`Φᵀ M Φ = 1` and `Φᵀ K Φ = diag(μ)`, and let `α`, `β` be real numbers. Then the
[Rayleigh damping matrix](rayleigh-damping.md) becomes diagonal:

`Φᵀ (α M + β K) Φ = diag(α + β μ_j)`.

For an oscillatory mode (`μ_j = ω_j² > 0`) the modal coefficient `α + β μ_j` is `2 ζ_j ω_j`, with
damping ratio `ζ_j`; a rigid mode (`μ_j = 0`) has coefficient `α`. Repeated values of `μ` are
allowed.
