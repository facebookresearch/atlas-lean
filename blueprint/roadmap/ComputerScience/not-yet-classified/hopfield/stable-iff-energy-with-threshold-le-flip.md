# Stable states are single-flip local minima

Let `T` be a symmetric weight matrix
(`Matrix.IsSymm T`) and `U` any thresholds. Then a state `v` is stable if and only if, for every
neuron `i`, flipping bit `i` does not decrease the threshold energy:
`energyWithThreshold T U v ≤ energyWithThreshold T U (update v i (!vᵢ))`.
