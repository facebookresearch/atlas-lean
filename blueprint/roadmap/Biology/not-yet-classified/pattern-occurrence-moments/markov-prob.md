# Chain weight of a word

`π(w_0) ∏_{i + 1 < n} P(w_i, w_{i+1})` for a word `w` of length
`n ≥ 1`, and `1` for the empty word, for any real weights `π` and `P`. When `π` is a probability
vector and `P` a stochastic matrix (as under `IsStationaryChain π P`), it is the probability of
`w` under the chain started from `π`.
