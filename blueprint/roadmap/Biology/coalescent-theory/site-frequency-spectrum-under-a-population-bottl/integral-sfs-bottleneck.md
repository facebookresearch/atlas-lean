# Expected site frequency spectrum under a bottleneck

Let the genealogy of a sample of
`n` gene copies from a population with the bottleneck history `bottleneckSize a d f`
(`d ≥ 0`, `f > 0`) be Kingman's coalescent (holding times `K.T`, independent random-joining
block-size history `τ`) run through the Griffiths–Tavaré time change, so that the epoch with
`k` lineages lasts `T^b_k = G(V_k) - G(V_{k+1})` (`bottleneckTimes`). If, given this
genealogy, the count `ξ i` is integrable with conditional mean `(θ / 2) L^b_i` (neutral
infinite-sites mutation at rate `θ / 2` per lineage per unit of real time), then for
`1 ≤ i ≤ n - 1`, `E ξ_i = (θ / 2) ∑_{k=2}^{n} k C(n-i-1, k-2) / C(n-1, k-1) · E T^b_k`.
