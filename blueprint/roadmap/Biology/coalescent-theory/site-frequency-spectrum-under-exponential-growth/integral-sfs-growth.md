# Expected site frequency spectrum under exponential growth

Let the genealogy of a
sample of `n` gene copies from a population that has grown exponentially at rate `ρ ≥ 0` be
Kingman's coalescent (holding times `K.T`, independent random-joining block-size history `τ`)
run through the Griffiths–Tavaré time change, so that the epoch with `k` lineages lasts
`T^ρ_k = G(V_k) - G(V_{k+1})` (`growthTimes`). If, given this genealogy, the count `ξ i` is
integrable with conditional mean `(θ / 2) L^ρ_i` (neutral infinite-sites mutation at rate
`θ / 2` per lineage per unit of real time), then for `1 ≤ i ≤ n - 1`,
`E ξ_i = (θ / 2) ∑_{k=2}^{n} k C(n-i-1, k-2) / C(n-1, k-1) · E T^ρ_k`.
The independence of the time-changed holding times and the topology, a hypothesis of
`VariableSFS.integral_sfs_of_indep`, is derived here from that of the Kingman ones.
