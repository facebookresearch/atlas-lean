# Generic convergence of the positive feedback loop

**Generic convergence of the positive feedback loop** (Angeli–Sontag 2004, Theorem 2, second
part). Let `sys` be a single-input single-output system (positivity cone `K`, state space `X`
equal to the closure of its interior, differentiable `f`, and a solution map `φ` giving, for every
`ξ ∈ X` and every input `u`, the unique solution from `ξ` on `[0, ∞)` that stays in `X`) that is
monotone, with a non-degenerate input-to-state characteristic `kX` on `U`; assume `h(X) ⊆ U`, and
let `ψ t ξ` be the solution map of the closed loop `ẋ = f(x, h(x))`: for `ξ ∈ X`, `t ↦ ψ t ξ` is a
solution on `[0, ∞)` that stays in `X`. Suppose the input/output characteristic `kY = h ∘ kX` has
non-degenerate fixed points on `U`, the closed loop is strongly monotone (`ξ₁ - ξ₂ ∈ K` and
`ξ₁ ≠ ξ₂` imply `ψ t ξ₁ - ψ t ξ₂ ∈ int K` for every `t > 0`), and every closed-loop trajectory
from `X` is bounded. Then for Lebesgue-almost every `ξ ∈ X` there is a fixed point `u ∈ U` of
`kY` with `kY'(u) < 1` such that `ψ t ξ → kX u` as `t → ∞`.

## Sources

- D. Angeli, E. D. Sontag, Systems Control Lett. 51 (2004) 185–202, Theorem 2.
