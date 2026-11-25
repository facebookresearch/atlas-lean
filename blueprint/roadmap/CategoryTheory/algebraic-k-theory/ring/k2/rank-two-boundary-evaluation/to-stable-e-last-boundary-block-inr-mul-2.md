# To Stable E last Boundary Block inr mul inl mem range imp eq one

Arbitrary-rank reverse-order via inverse symmetry: `toStableE (lastBoundaryBlock n
(inr r) * lastBoundaryBlock n (inl c))` in `E_n` forces `r=1`, `c=1`. Uses subgroup
inverse closure, `map_inv`, `mul_inv_rev`, `MonoidHom.map_inv` for column/row, then inverts
equalities. Ordered products preserved; no alternating-word, no torus mult, no cocycle,
no kernel.
