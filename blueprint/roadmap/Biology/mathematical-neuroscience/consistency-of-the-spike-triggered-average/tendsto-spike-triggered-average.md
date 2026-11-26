# Consistency of the spike-triggered average

**Consistency of the spike-triggered average** (Paninski 2003). Let `P` be a probability
measure and `Z i = (x_i, y_i)` stimulus–response pairs that are pairwise independent and
identically distributed. Assume the stimulus law `ν` of `x_0` is elliptically symmetric with
finite second moments, `y_0 ≥ 0`, `y_0` and `y_0 ‖x_0‖` are integrable, and the LN model holds:
`E[y_0 φ(x_0)] = E[g(k · x_0) φ(x_0)]` for every bounded measurable `φ`, for a measurable
`g ≥ 0` with `g(k · x_0)` and `g(k · x_0) (k · x_0)` integrable, `E[g(k · x_0)] > 0`,
`kᵀ Σ k > 0`, and nonzero gain `E[g(k · x_0) (k · x_0)] ≠ 0`. Then almost surely
`STA_N → κ Σ k` with nonzero scalar
`κ = E[g(k · x_0) (k · x_0)] / (E[g(k · x_0)] · kᵀ Σ k) ≠ 0`. Since `ν` is elliptically symmetric
(`Σ = α A Aᵀ` with `A` invertible) and `kᵀ Σ k > 0` forces `α > 0`, `Σ` is invertible and
`Σ⁻¹ STA_N` converges almost surely to the nonzero multiple `κ k` of the filter `k`.

## Sources

- L. Paninski, "Convergence properties of three spike-triggered analysis techniques", Network: Comput. Neural Syst. 14 (2003) 437–464, Theorem 1.
