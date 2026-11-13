# Converging together in a pseudo-emetric space

**Converging together in a pseudo-emetric space** (Slutsky-type lemma; Billingsley (1999),
Theorem 3.1). If `Y n → Z` in distribution, and for every `ε > 0` the paths `X n` and `Y n`
are `ε`-close outside measurable sets `A n` whose probabilities tend to `0`, then `X n → Z`
in distribution.

Mathlib's `tendstoInDistribution_of_tendstoInMeasure_sub` needs a seminormed group; the J1
space is not one, so this version works with an arbitrary pseudo-emetric space and controls
the distance through explicit measurable bad sets (no measurability of `edist (X n) (Y n)`
is required).
