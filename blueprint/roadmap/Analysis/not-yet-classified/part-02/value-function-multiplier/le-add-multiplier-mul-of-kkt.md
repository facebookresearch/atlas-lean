# Le add multiplier mul of kkt

Shadow-price bound for a concave resource problem. Maximize `u y` subject to the resource
constraint `g y ≤ b`. Let `u` be concave and `g` convex on the whole space, both differentiable
at `x₀`, with `x₀` feasible at level `b₀` and a multiplier `lam ≥ 0` satisfying complementary
slackness `lam * (g x₀ - b₀) = 0` and stationarity `fderiv ℝ u x₀ = lam • fderiv ℝ g x₀`
(the KKT conditions of `karush_kuhn_tucker_inequality` for `-u` and `g - b₀`). Then every
`y` feasible at any level `b` satisfies `u y ≤ u x₀ + lam * (b - b₀)`. So `lam` is a
supergradient of the value function at `b₀` on the levels whose feasible set is nonempty, with no
differentiability of the value assumed.
