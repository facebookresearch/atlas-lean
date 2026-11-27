# Transport cost of a plan

For a ground cost `d : V → V → ℝ` and a matrix
`π : V → V → ℝ` on a finite type, the cost of the single plan `π` is
`∑ x, ∑ y, π x y * d x y`. For fixed probability vectors `S` and `T`, the infimum of
`transportCost d π` over couplings `π` of `S` and `T` is `earthmover d S T`.
