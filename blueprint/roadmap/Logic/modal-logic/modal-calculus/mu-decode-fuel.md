# Fuelled decoding of a μ-calculus number code

Fuelled decoding of a `muCode` number back to a formula. The fuel bounds the
recursion depth; `muDecode` supplies fuel `c + 1`, which exceeds every formula's
depth (see `depth_le_code`).
