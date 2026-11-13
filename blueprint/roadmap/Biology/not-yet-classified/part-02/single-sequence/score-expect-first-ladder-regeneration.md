# The ladder epochs form a renewal process

**The ladder epochs form a renewal process** (regeneration at the first ladder epoch): on
`{τ₊ = k}` the walk after `τ₊` is a fresh iid walk, independent of the ladder segment up to `τ₊`
(hence of the ladder height). For any functionals `H` of the segment and `G` of the remainder,
`E[H; τ₊ = k] · E[G]` factorizes. Iterating (`scoreProb_two_ladders`) the successive
(ladder epoch gap, ladder height) pairs are iid.
