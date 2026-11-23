# Expected site frequency spectrum under a Λ-coalescent

For a finite measure `Λ` on `[0, 1]`, a real `θ` and natural numbers `n` and `i`, the expected
site frequency spectrum is `E ξ_i = (θ / 2) E L_i`, where `E L_i` is the
[expected length](expected-length.md) of branches subtending `i` copies for the Λ-coalescent
started from `n` blocks of size `1`. The formula is defined for every real `θ`. For `Λ ≠ 0`,
`n ≥ 2` and `θ ≥ 0`, under neutral infinite-sites mutation at rate `θ / 2` per lineage, it is the
expected number of segregating sites whose derived allele is carried by exactly `i` of the `n`
sampled gene copies; for `θ < 0` it is not a count. The factor `θ / 2` divides by the constant
`2`. Inside `E L_i` the divisions by the total merger rate are read with `x / 0 = 0`; that rate is
`0` for `Λ = 0` and in states with fewer than two blocks, which therefore contribute nothing, so
`E ξ_i = 0` for `Λ = 0` and for `n ≤ 1`. At `Λ = 0` with `n ≥ 2` this value `0` is not in
general the expected count: the sampled lineages never merge, so for `θ > 0` the expected number
of singleton sites (`i = 1`) is infinite.
