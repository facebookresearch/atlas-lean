# The path bridge

A chain path whose birth counting path is nondecreasing (as unit Poisson
paths are, almost surely) gives a chain path `toPath S E I R` of the stochastic mass-action system
`chainCRN` in the sense of `StochasticCRNLLN.IsChainPath`. The propensities along `toPath` are
constant on `(-∞, 0]`; on `[0, t]` every count is at most the initial total plus the births up to
time `t` (`total_le`), so they are bounded.
