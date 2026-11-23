# Alt Merge Sum

The alternating sum `∑_{m=0}^{b-k} (b-k choose m) (-1)^m q_{k+m}` of the merger probabilities
`q_j = mergeProb j`: by inclusion–exclusion, the probability that `k` given lineages among `b`
share a parent that none of the other `b - k` lineages has (`sampleProb_inclusionExclusion`).
Divided by `c_N` it converges to Pitman's rate `λ_{b,k} = ∫ x^(k-2) (1-x)^(b-k) Λ(dx)`.
