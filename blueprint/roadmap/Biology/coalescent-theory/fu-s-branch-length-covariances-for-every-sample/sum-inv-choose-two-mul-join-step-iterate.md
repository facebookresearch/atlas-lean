# Time-weighted block statistics of random joining as a clade sum

Let `k` be a natural number, `b` a list of `k` natural numbers (block sizes) and `φ` any function
from the natural numbers to the reals. Let `J` be the
[transition operator of random joining](../expected-site-frequency-spectrum/join-step.md) and `G(y) = ∑_{x ∈ y} φ(x)` for a
list `y`. Then

`∑_{l=2}^{k} C(l, 2)⁻¹ (J^{k-l} G)(b) = ∑_s w_k(|s|) φ(Σ s)`,

where `s` runs over the `2^k` sub-multisets of `b`, one for each set of positions, `|s|` is the
number of elements of `s`, `Σ s` their sum, and `w_k(m) = 2 / (m C(k, m))` for `1 ≤ m < k` and `0`
otherwise: the right side is the [clade statistic](clade-stat.md) of `b`. Both sides are `0` when
`k ≤ 1`.

By [the finite-support theorem for random joining](../expected-site-frequency-spectrum/exists-finset-random-joining.md),
`(J^{k-l} G)(b)` is the expected value of `∑ φ(|B|)` over the `l` blocks `B` present after `k - l`
steps of random joining from `b`, and `1 / C(l, 2)` is the mean holding time of Kingman's coalescent
with `l` lineages. So the left side is the expected value of
`∑_{l=2}^{k} C(l, 2)⁻¹ ∑_{blocks B at level l} φ(|B|)`.
