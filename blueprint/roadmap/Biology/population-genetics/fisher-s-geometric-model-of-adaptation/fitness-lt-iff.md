# For fitness decreasing with distance, gain means closer to optimum

Let fitness be a strictly decreasing function `φ : ℝ → ℝ` of the distance to the optimum `0`. For
all `a, u ∈ ℝⁿ` and every real `r`, `φ(‖a‖) < φ(‖a + r u‖)` if and only if `‖a + r u‖ < ‖a‖`:
a mutation raises fitness exactly when it moves the phenotype strictly closer to the optimum.
