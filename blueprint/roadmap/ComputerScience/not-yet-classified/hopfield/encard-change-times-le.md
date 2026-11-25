# At most `2 ^ N - 1` changes

Let `T` be a weight matrix that is symmetric off the diagonal
(`OffDiagSymmetric T`) and `U` any thresholds. Then for every schedule `σ` and initial state `v₀`,
the set of attempt indices at which the state changes has at most `2 ^ N - 1` elements:
`(changeTimes T U σ v₀).encard ≤ 2 ^ N - 1`.
