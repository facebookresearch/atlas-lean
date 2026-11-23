# Runoff volume is the catchment area times the rainfall-excess depth

Let the rainfall excess `p` (depth per step) vanish from step `n` on and the unit response `u`
(discharge per unit depth) from step `m` on, and let the unit response integrate to the catchment
area `A` over the time step `dt`, `dt * ∑_{j < m} u j = A` (a unit depth over the catchment). Then
the runoff volume of the [discrete convolution](discrete-convolution.md) `q` is
`dt * ∑_{k < n + m} q k = A * ∑_{i < n} p i`, the area times the total rainfall-excess depth.
