# Local circular submean condition for a nonpositive function

For `u : ℂ→EReal` and
`D⊆ℂ`, `IsNonpositiveSubharmonicOn u D` requires `D` connected, `u` upper semicontinuous
on `D`, `u(z)≤0` for every `z∈D`, and some `z∈D` with `u(z)≠-∞`. For each `z∈D` there must
exist `ε>0` with `closedBall z ε⊆D` such that for every `0<r<ε`,

`negativeCircleAverage u z r ≤ (-u(z)).toENNReal`,

where `negativeCircleAverage u z r=(1/(2π))∫⁻_{θ∈(0,2π]} (-u(z+r exp(iθ))).toENNReal dθ`.
Negative-infinite values are allowed, while the existence clause excludes the identically
negative-infinite function.
