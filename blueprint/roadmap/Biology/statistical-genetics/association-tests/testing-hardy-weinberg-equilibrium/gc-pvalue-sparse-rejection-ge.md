# Genomic control with `lam ≤ 1` leaves the sparse test anti-conservative

For every
`lam ∈ (0, 1]` the level-`0.05` genomic-control test still rejects with null probability at
least `1/19 > 0.05` in the sparse HWE model. This range is **not** the clipped-genomic-control
regime: clipping floors the factor actually used at `1`, so a clipped factor satisfies
`lam ≥ 1` and `lam < 1` never occurs after clipping (dividing by a smaller number inflates
the statistic and makes rejection easier). The `lam = 1` endpoint is the clipped boundary:
when the estimated inflation is at most `1`, clipping uses `lam = 1`, and the test still
rejects with null probability at least `1/19`.
