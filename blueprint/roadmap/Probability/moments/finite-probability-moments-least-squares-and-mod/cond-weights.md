# Cond Weights

Assume that equality on `Ω` is decidable.

The weights normalized on the event `A`: `p ω / P(A)` on `A` and `0` off it. The proof of
`0 < P(A)` is part of the definition, so a null event has no normalized weights. For nonnegative
weights they are a finite distribution (`condWeights_isDistribution`).
