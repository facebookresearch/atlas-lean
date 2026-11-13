# Path Weight

The weight of a list of nodes `[v₀, v₁, …, vₘ]` read as the directed path
`v₀ → v₁ → ⋯ → vₘ` for the coefficient matrix `B`, where `B i j` is the coefficient of node
`j` in the equation of node `i` (the edge `j → i`): the product
`B v₁ v₀ * B v₂ v₁ * ⋯ * B vₘ vₘ₋₁` of the edge coefficients. A one-node list has weight `1`.
