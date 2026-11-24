# Stable Steinberg Finite Weyl Hurwitz Normal Form

Weighted Weyl normal form over the finite torus.

Purpose: factor the head-left product of a coefficient-carrying Weyl word
whose label projection has permutation product one as `c * t`, with `c` in
the torus cocycle subgroup and `t` in the rank-`n` finite torus subgroup.
Orientation is head-left throughout, matching `weightedWeylProd`.
Hypotheses: `[Field F]` only, a paired word `wc`, and product one of its
label projection. The factors are existential.

Nonclaims: normal form only; no kernel generation, finite-stage/`List.ofFn`
bridge, inverse identity, naturality, TWT, or Matsumoto claim.
