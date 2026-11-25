# The one-coordinate energy identity with thresholds

Let `T` be a symmetric weight matrix
(`Matrix.IsSymm T`) and `U` any thresholds. Then for every state `v`, neuron `i` and bit `a`, the
difference `energyWithThreshold T U (update v i a) - energyWithThreshold T U v` equals
`-(a - vᵢ) · (localField T v i - Uᵢ)`, with bits read as 0/1.
