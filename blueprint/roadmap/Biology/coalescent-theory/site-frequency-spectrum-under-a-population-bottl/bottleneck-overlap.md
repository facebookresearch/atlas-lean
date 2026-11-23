# Length of the part of a window before a given time

For real numbers `a`, `w` and `u`, let `O_{a,w}(u) = min(max(u - a, 0), w)`. For `w ≥ 0` it is
the length `|(-∞, u] ∩ [a, a + w]|` of the part of the window `[a, a + w]` before time `u`, which
equals `|[0, u] ∩ [a, a + w]|` when `a ≥ 0`. For `w < 0` the window is empty, but the clipped
expression is `w` for every `u`: a negative number, not the length `0` of the empty window.
