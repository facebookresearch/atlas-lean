# Weighted Weyl Prod

Head-left product of a coefficient-carrying Weyl word.

Purpose: product meaning of a paired label-coefficient word, with each entry
`(a, u)` denoting `weylOfSwapLabel a u`. Orientation is head-left, matching
`wordProd` and `List.prod`: the head entry is the leftmost factor.
Hypotheses: `[Ring R]` only. Nonclaims: no trace transport, deletion,
torus/cocycle, descent, `List.ofFn` bridge, kernel, TWT, or Matsumoto
content.
