# IOSystem

A single-input single-output system `ẋ = f(x, u)`, `y = h(x)` with state space `X`, input set
`U`, positivity cone `K` on states and solution map `φ t ξ u`. As the source assumes, `X` is the
closure of an open set, and for every `ξ ∈ X` and every input `u` the solution `t ↦ φ t ξ u`
exists on `[0, ∞)`, stays in `X`, and is the unique solution with these properties. The vector
field `f` (jointly in `(x, u)`) and the output map `h` are continuously differentiable (`C¹`):
the source takes `f` differentiable for simplicity and `h` monotone, and this encoding takes `C¹`
for the linearization of the closed loop and the generic convergence argument.
