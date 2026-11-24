# Exists unitary mul eq of isometry

Any two `out × inp` isometries with the same finite domain differ by a
left-multiplied square unitary on `out`. The input is allowed to be `Finite`
and possibly empty; the empty case is handled explicitly, and a nonempty input
rules out empty output from `Vᴴ * V = 1`. The proof converts to Euclidean
lin maps, builds range linear isometry equivalences, extends with
`LinearIsometry.extend`, uses finite-dimensional injectivity iff surjectivity,
and converts back to a unitary matrix.
