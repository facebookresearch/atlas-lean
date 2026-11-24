# Two-compartment observability determinant

For real rates `k10`, `k12`, `k21` and a central volume `V1`, the observability matrix
`O = [[1 / V1, 0], [-(k10 + k12) / V1, k21 / V1]]` of the
[two-compartment generator](../two-compartment-pharmacokinetics/pk2-generator.md)
`M = [[-(k10 + k12), k21], [k12, -k21]]` with central output `H = (1 / V1, 0)` (rows `H` and `H M`)
has determinant `det O = k21 / V1 ^ 2`. This holds for all real inputs: with the convention
`x / 0 = 0`, at `V1 = 0` the matrix is zero and both sides are `0`. So the determinant is nonzero
exactly when `k21 ≠ 0` and `V1 ≠ 0`, the case where
[the two output jets identify the state](jet-injective-of-k21-ne-zero.md). In the model the rates
are nonnegative and the volume is positive.
