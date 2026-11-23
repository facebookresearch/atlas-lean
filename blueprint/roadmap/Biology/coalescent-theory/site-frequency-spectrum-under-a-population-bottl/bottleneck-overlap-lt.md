# The window overlap grows strictly across the window

For real numbers `a`, `w > 0`, `u` and `v` with `u < v`, `u < a + w` and `a < v`, the
[overlap](bottleneck-overlap.md) `O_{a,w}(u) = min(max(u - a, 0), w)` satisfies
`O_{a,w}(u) < O_{a,w}(v)`: the interval `[u, v]` meets the window `[a, a + w]` in an interval of
positive length.
