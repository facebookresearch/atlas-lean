# Occupancy Equiv

Stationary randomized policies, represented by `IsRowStochastic` rows, correspond bijectively
to **all** nonnegative solutions of the discounted flow equations with positive initial weights.
The forward map divides the normalized occupancy by `1 - γ`; the inverse divides each entry by
its row sum.
