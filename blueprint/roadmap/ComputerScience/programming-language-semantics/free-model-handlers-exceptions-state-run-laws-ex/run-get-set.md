# Reading and writing back the state

For a continuation `k`, reading the state and writing it back before `k`
behaves as `k`: the get-put equation. The equation holds after running the
computation with `run` from any initial state `s0`; it is not an equality of
the unevaluated computations.
