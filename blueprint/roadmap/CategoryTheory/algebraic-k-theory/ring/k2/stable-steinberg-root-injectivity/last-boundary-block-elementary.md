# Last Boundary Block Elementary

Finite elementary representative of a single last-boundary block at rank
`n+1` over an arbitrary ring `R` (universe `u`).

Orientation: `Sum.inl c` is the last-column block (upper unit),
`Sum.inr r` is the last-row block (lower unit). Dispatches to the private
`colSubgroupHom n` and `rowSubgroupHom n` subgroup homs, reusing their
`BlockElementary` block machinery. Finite rank is exactly `n+1`.

Proves evaluation only; makes no pivot, scalar-equation, alternation,
kernel-generation, finite-stage landing, strict-decrease, cocycle,
naturality, or Matsumoto claim.
