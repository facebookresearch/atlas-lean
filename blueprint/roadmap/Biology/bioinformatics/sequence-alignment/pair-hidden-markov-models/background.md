# Independence-model weight of a sequence pair

The independence-model weight for `xs` and `ys` (Durbin et al., chapter 4):
`η² (1 - η)^(|xs| + |ys|) ∏ q xs ∏ q ys`. This is a probability when `q` is a
normalized nonnegative distribution and `0 < η < 1`, as required by `LinearGapLogOdds`.
