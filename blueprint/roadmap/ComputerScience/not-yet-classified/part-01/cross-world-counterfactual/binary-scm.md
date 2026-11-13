# Binary SCM

A recursive structural causal model on two observed binary nodes `X → Y` with exogenous
noise in a finite type `U`: noise weights `pU`, structural equations `X = fX u` and
`Y = fY X u`. Counterfactuals use the same noise `u` in every intervened world. The structure
does not force `pU` to be a probability mass function; that is the predicate `IsNoiseLaw`,
which the two concrete witnesses below are proved to satisfy.
