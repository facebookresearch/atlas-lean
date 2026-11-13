# The Lindley process has the law of the walk maximum

`P(Wₙ ≥ t) = P(max_{k ≤ n} S_k ≥ t)`,
so at a Cramér root `θ ≥ 0` the reflected walk is tight, `P(Wₙ ≥ t) ≤ e^{-θ t}` uniformly in
`n` (`scoreProb_le_walkMax_le`).
