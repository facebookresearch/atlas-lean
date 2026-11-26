# Grouped event rates

For nonnegative event rates and a state `x` with nonzero total rate,
the holding rate at `x` times the probability that the next event step lands in a state `y` is
`∑ e ∈ {e | succ e x = y}, rate e x`, the rate of the events leading from `x` to `y` (for `y = x`,
of the events that leave `x` unchanged).
