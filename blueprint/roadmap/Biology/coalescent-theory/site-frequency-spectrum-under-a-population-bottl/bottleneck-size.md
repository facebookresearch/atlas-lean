# Bottleneck population-size history

For real numbers `a`, `d`, `f` and `s`, let `η(s) = f` if `a ≤ s < a + d` and `η(s) = 1`
otherwise. For `d ≤ 0` the window `[a, a + d)` is empty and `η` is constantly `1`.

With `a ≥ 0`, `d ≥ 0` and `f > 0`, `η(s)` is the size at time `s ≥ 0` before the present,
relative to a reference size `N₀` (time in units of `2N₀` generations), of a population that had
size `N₀` until time `a + d` before the present, then size `f N₀` for `d` time units, and has
had size `N₀` again for the last `a` time units. `N₀` is the present size when `a > 0`, `d = 0`
or `f = 1`; for `a = 0 < d` the window contains the present and the present size is `f N₀`. For
`d > 0`, `f < 1` is a bottleneck and `f > 1` a temporary expansion; `f = 1` or `d = 0` gives a
constant population.
