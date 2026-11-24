# Coalescent with killing

Fix a sample size `n`, a real `θ` and a measure `μ` on a measurable space `Ω`. A coalescent with
killing of the sample under infinite-alleles mutation (time in units of `2N` generations, scaled
mutation rate `θ = 4Nu`, mutations at rate `θ / 2` per lineage) consists of real functions `C k`
and `M k` on `Ω`, one of each for every natural number `k`, such that

- for every level `2 ≤ k ≤ n`, `C k` has, under `μ`, the exponential law of rate
  `k (k - 1) / 2` (each pair of lineages coalesces at rate `1`), and `M k` the exponential law of
  rate `k θ / 2` (each lineage mutates at rate `θ / 2`);
- the functions `M k` and `C k`, `2 ≤ k ≤ n`, are mutually independent under `μ`.

The values of `C k` and `M k` for `k` outside `[2, n]` are unconstrained. The exponential law of a
rate `λ ≤ 0` is taken to be the zero measure, so the conditions are meant for `θ > 0`: for `n ≥ 2`
and `θ ≤ 0` no coalescent with killing exists, since the laws of `C 2` and `M 2` are both images
of `μ`, hence of equal total mass, while the first has mass `1` and the second, of rate `θ ≤ 0`,
mass `0`. For `n < 2` there are no levels and `θ` plays no role.

While the genealogy has `k` lineages, `C k` is the waiting time to the next coalescence and `M k`
the waiting time to the next mutation; whichever comes first reduces the number of lineages to
`k - 1`. A coalescence merges two lineages; a mutation founds an allele carried by exactly the
genes descending from that lineage, which is then removed ("killed") because earlier mutations on
it are invisible in the sample. By memorylessness the clocks restart at each level, so one
independent pair of clocks per level determines the sequence of events, as for the
[holding times of Kingman's coalescent](../../coalescent-theory/kingman-s-coalescent-and-watterson-s-estimator/kingman-times.md).
