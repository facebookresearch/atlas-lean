# Minrun Next N output bounds

Arbitrarily many calls from `merge_init` pass every signed-overflow
assertion and emit only targets in `1 .. 64`.
This theorem does not use exact quotient/remainder mask equivalence.
