# Individual fairness as a Lipschitz condition

For a task metric `d : V → V → ℝ`
(any real-valued function) and a randomized classifier `M : V → O → ℝ` with finitely many
outcomes, `IsLipschitzFair d M` holds when every row `M x` is a probability distribution
on the outcomes (nonnegative entries summing to `1`) and the total variation distance
between the outcome distributions of any two individuals is at most their task-metric
distance: `tvDist (M x) (M y) ≤ d x y` for all `x, y`.
