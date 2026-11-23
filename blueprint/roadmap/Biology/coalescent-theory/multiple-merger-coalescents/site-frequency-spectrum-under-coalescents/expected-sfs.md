# Expected site frequency spectrum under a Λ-coalescent

For a finite measure `Λ` on `[0, 1]`, a real `θ` and natural numbers `n` and `i`, the expected
site frequency spectrum is `E ξ_i = (θ / 2) E L_i`, where `E L_i` is the
[expected length](expected-length.md) of branches subtending `i` copies for the Λ-coalescent
started from `n` blocks of size `1`. Under neutral infinite-sites mutation at rate `θ / 2` per
lineage it is the expected number of segregating sites whose derived allele is carried by
exactly `i` of the `n` sampled gene copies. The factor `θ / 2` divides by the constant `2`.
Inside `E L_i` the divisions by the total merger rate are read with `x / 0 = 0`; that rate is `0`
for `Λ = 0` and in states with fewer than two blocks, which therefore contribute nothing, so
`E ξ_i = 0` for `Λ = 0` and for `n ≤ 1`. The intended domain is `Λ ≠ 0` and `n ≥ 2`.
