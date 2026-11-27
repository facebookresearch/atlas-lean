# Point masses of the jump distribution

For nonnegative event rates and a state `x` with
nonzero total rate `λ(x)`, the next event step from `x` lands in each state `y` with probability
`(∑ e ∈ {e | succ e x = y}, rate e x) / λ(x)`: events with the same successor add up, and events
that leave `x` unchanged give the mass at `y = x`.
