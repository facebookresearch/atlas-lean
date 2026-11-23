# The window overlap grows at most as fast as time

For real numbers `a`, `w ≥ 0`, `u` and `v` with `u ≤ v`, the
[overlap](bottleneck-overlap.md) `O_{a,w}(u) = min(max(u - a, 0), w)` satisfies
`O_{a,w}(v) - O_{a,w}(u) ≤ v - u`. Since the overlap is
[nondecreasing](bottleneck-overlap-mono.md), it is `1`-Lipschitz in `u` for `w ≥ 0`.
