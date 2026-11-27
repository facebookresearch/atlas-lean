# Reading right after writing

For a state `s`, a continuation `k` and any initial state `s0`, running the computation that writes `s`, then reads the state and passes it to `k`, gives the same result as running the computation that writes `s` and then continues with `k s`:

    run (set s >> (get >>= k)) s0 = run (set s >> k s) s0

So `k` both receives `s` and starts in state `s`: the write is kept and only the read is removed. The equation holds after running with `run` from any initial state; it is not an equality of the unevaluated computations.
