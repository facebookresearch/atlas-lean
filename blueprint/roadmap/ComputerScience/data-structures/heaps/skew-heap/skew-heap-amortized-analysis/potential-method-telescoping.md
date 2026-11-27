# Potential method telescoping

Ch. 19's telescoping sum: for a sequence of operations
`s₀, …, sₙ` with `s_{i+1} = f s_i`,
`∑ A_f s_i = ∑ T_f s_i + Φ sₙ - Φ s₀`. In the framework this is
`t_sum_a_sum`, for operation *histories* (rose trees) rather than
just sequences; the initial potential `Φ s₀` is `Φ Leaf = 0`,
because a well-formed history's leaves are `Empty` operations whose
state is `Leaf`.
