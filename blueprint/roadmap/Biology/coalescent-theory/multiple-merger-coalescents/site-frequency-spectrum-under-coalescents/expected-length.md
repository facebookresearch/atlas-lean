# Expected Length

The **expected total length of branches subtending exactly `i` sample copies**, for the
Λ-coalescent started from the block sizes `b`: the expected occupation sum
`∑_j E [holdingCount Λ i (X_j)]` over the jump chain `X`. For `Λ ≠ 0`, jumps after the first
`b.length` contribute nothing (`expectedLength_eq_sum`). For `Λ = 0` nothing ever merges, the
true length is infinite, and the definition returns the junk value `0`.
