# Bottleneck population-size history

For real numbers `a`, `d`, `f` and `s`, let `η(s) = f` if `a ≤ s < a + d` and `η(s) = 1`
otherwise. With `a ≥ 0`, `d ≥ 0` and `f > 0`, `η(s)` is the relative size at time `s ≥ 0`
before the present (in units of `2N₀` generations, `N₀` the present size) of a population that
was at its present size until time `a + d` before the present, then had `f` times that size for
`d` time units, and has been back at its present size for the last `a` time units: `f < 1` is a
bottleneck, `f > 1` a temporary expansion, and `f = 1` or `d = 0` a constant population. For
`d ≤ 0` the window `[a, a + d)` is empty and `η` is constantly `1`.
