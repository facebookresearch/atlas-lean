# Two writes in a row

For states `s`, `s'` and a continuation `k`, writing `s` then `s'` behaves as
writing `s'`: the first write is discarded (the put-put equation). The
equation holds after running the computation with `run` from any initial state
`s0`; it is not an equality of the unevaluated computations.
