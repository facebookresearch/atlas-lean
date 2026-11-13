# Fuelled decoding of linear μ-calculus codes

Fuelled decoding of a `linearMuCode` number back to a formula. The fuel bounds
the recursion depth; `linearMuDecode` supplies fuel `c + 1`, which exceeds every
formula's depth (see `linearDepth_le_code`).
