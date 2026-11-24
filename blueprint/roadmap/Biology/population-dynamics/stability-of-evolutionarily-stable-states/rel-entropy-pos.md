# The relative entropy is positive away from p

For a finite set `ι` and vectors `p, y : ι → ℝ` in the interior of the simplex (`p_i > 0` and
`y_i > 0` for every `i`, `∑_i p_i = ∑_i y_i = 1`) with `y ≠ p`, the
[relative entropy](../../../ComputerScience/machine-learning/bayesian-inference-and-sampling/mean-field-variational-inference/kl.md)
`V_p(y) = ∑_i p_i (log p_i - log y_i)` satisfies `V_p(y) > 0`. The proof uses `log z < z - 1` for
`z > 0`, `z ≠ 1`.
