# Lattice one-sequence tail input

**Lattice one-sequence tail input** for the maximal segment score `M_L` of `L` iid scores with
law `(q, f)` and lattice span `h`: `P(M_L > t) = (K + o(1)) L e^{-θ t⁺}`, `t⁺ = latticeAbove h t`,
uniformly as `L → ∞` and `L e^{-θ t} → 0` over thresholds `t ≤ η L`. This is `OneSequenceTail`
with `e^{-θ t}` replaced by `e^{-θ t⁺}` on the right, the form of the lattice case of
Karlin–Dembo (1992); it is a hypothesis here, not derived.
