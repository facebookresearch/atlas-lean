# Large-population limit

Along a sequence of models `k` with population sizes
`N k → ∞` in which all but `o(N k)` individuals are initially susceptible (an index case inside
the population is one of these `o(N k)` individuals), the probability that the epidemic is
extinct by generation `n` converges to the branching-process value
`P(Z n = 0) = f^[n]&#40;0)`. As `n → ∞` these values increase to the extinction probability `q`
(`tendsto_law_real_zero`): `q` is the probability of a minor outbreak in the sense of the
module docstring.
