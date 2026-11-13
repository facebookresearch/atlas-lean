# Restart law at a fixed time

**Restart law at a fixed time** (cf. the Markov property, Norris 1997, §2.8), for events of
`X s` and of the path after `s` only: for the chain started at `i`, the probability that
`X s = k` and that the path after `s` lies in a measurable set `B` is `exp (s Q) i k` times the
probability that the chain started at `k` lies in `B`. This is weaker than the Markov property
with respect to the natural filtration: arbitrary events of the path before `s` are not covered
(only through the finite-dimensional distributions, `ctmcInputMeasure_real_ctmcPath_fdd`).
