# Poisson–Gamma duality

The Gamma law of shape `k + 1` and rate `r` (Mathlib's
`gammaMeasure`) has upper tail `P(Gamma(k + 1, r) > x) = F_k(r x)`. This is the Erlang tail
`gammaMeasure_real_Ioi_natCast_add_one` in `GammaMoments`, rewritten with the definition of
`poissonCDF`.
