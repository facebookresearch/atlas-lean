# Time-weighted future block counts of random joining

For a list `b` of `k` block sizes
and a statistic `φ` of a block size, the expected value of `∑_{l=2}^{k} T̄_l ∑_{blocks B at level
l} φ(|B|)` under random joining from `b`, with `T̄_l = 1 / C(l, 2)`, is the clade statistic
`∑_{s ⊆ b} 2 / (|s| C(k, |s|)) · φ(Σ s)` (over sub-multisets `s` with `1 ≤ |s| < k`).
