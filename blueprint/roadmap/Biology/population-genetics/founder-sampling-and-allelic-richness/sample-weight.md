# Weight of an ordered founder sample

For real allele frequencies `p` on a set `A` of alleles and an ordered sample
`s = (s_1, …, s_k)` of `k` gene copies, the sample weight is `∏_{j=1}^k p(s_j)`, the product of
the frequencies of the drawn alleles (`1` for `k = 0`). For admissible frequencies (`A` finite,
`p ≥ 0` and `∑_a p(a) = 1`) it is the probability of the ordered sample `s` when the `k` copies are
drawn independently with replacement from the source population; for other frequencies it is the
same product, which need not be a probability.
