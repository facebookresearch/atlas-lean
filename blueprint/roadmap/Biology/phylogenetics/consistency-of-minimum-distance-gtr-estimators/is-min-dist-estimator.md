# Is Min Dist Estimator

`est` is a **minimum-distance estimator** for the model `law` given frequency estimates `freq`:
for every `n` and `ω`, `est n ω` minimizes `θ ↦ dist (law θ) (freq n ω)` over the whole parameter
space. With `freq = empiricalFreq X` this is the estimator of the GTR corollary.
