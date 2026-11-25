# Hopfield's Eq. (8)

**Hopfield's Eq. [8]** for a unilateral change. Let `T` be a symmetric weight matrix
(`Matrix.IsSymm T`). Then for every state `v`, neuron `i` and bit `a`, setting neuron `i` to `a`
changes the zero-threshold energy by
`energy T (update v i a) - energy T v = -(a - vᵢ) · localField T v i`, with bits read as 0/1.
