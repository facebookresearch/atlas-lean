# Verify

The **Merkle verifier**: accept the claim "leaf `i` of an `n`-leaf tree with root `r` is `x`"
with path `p` when `i < n` and recomputing from `x` and `p` for the height `Nat.clog 2 n` of the
tree gives `r`. `recompute` recurses once per level, so verification takes `⌈log₂ n⌉` rounds,
whatever the path.
