# Local existence of mild solutions, uniform on bounded sets of initial data

Let `S` be a C₀ semigroup on a real Banach space `X` and let `F : X → X` be Lipschitz on
bounded sets. For every radius `r` there are a time `T > 0` and a bound `R` such that every
initial value `x₀` with `‖x₀‖ ≤ r` has a continuous mild solution of `u' = A u + F u`,
`u 0 = x₀` on `[0, T]` with `‖u t‖ ≤ R` there. Both `T` and `R` are chosen before `x₀`, so
together with `exists_norm_sub_le_of_norm_le` the solution map is Lipschitz on the ball.
The proof is the Banach fixed-point theorem for the Duhamel map on `C([0, T], X)`.
