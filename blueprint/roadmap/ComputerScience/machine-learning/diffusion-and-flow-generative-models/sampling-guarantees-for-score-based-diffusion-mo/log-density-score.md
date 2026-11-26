# Score of a density

The score `∇ log ρ` of a density `ρ`, through Mathlib's `gradient`
(`0` at points where `log ∘ ρ` is not differentiable). The gradient is taken in the space variable,
as in score matching; `MathlibExt.Probability.Statistics.VectorInference.score` is instead the
gradient `∇_θ log p θ x` in the parameter of a statistical model.
