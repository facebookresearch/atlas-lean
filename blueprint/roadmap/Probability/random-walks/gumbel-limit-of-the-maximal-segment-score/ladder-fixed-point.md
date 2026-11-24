# Descending-ladder fixed point for an excursion height

For a measure `P` on `Ω` and a real random variable `Y` (an excursion height), a descending-ladder
fixed point consists of measurable real random variables `D` and `M'` with `D ≤ 0` and `M' ≥ 0`
almost surely, `M'` independent of the pair `(Y, D)`, and `P(max(Y, D + M') > t) = P(M' > t)` for
every real `t`. In the intended reading, `Y` is the height of the first ladder excursion of a score
walk `S`, `D = S_T` is the walk at its first descending ladder epoch `T`,
`M' = sup_{k ≥ T} (S_k - S_T)` is the all-time maximum of the walk after `T`, and `max(Y, D + M')`
is the all-time maximum of the whole walk; these are the facts that the strong Markov property at
`T` provides; the structure takes them as hypotheses.
