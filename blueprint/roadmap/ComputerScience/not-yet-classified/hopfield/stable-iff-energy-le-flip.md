# Stable states are single-flip local minima at zero threshold

**Stable states are single-flip local minima at zero threshold** (Eq. [7]). Let `T` be a
symmetric weight matrix (`Matrix.IsSymm T`). Then a state `v` is stable for the zero-threshold
dynamics if and only if, for every neuron `i`, flipping bit `i` does not decrease the energy:
`energy T v ≤ energy T (update v i (!vᵢ))`.
