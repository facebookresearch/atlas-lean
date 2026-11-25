# Reading right after writing

For a state `s` and a continuation `k`, reading right after writing `s` passes
`s` to `k`: the put-get equation. The equation holds after running the
computation with `run` from any initial state `s0`; it is not an equality of
the unevaluated computations.
