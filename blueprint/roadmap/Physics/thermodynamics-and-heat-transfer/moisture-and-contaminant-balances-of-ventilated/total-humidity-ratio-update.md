# Total humidity ratio over one inventory interval

Let `V` be a finite set of nodes and `E` a finite set of arcs, with tail and head maps
`tail, head : E → V`, arc transfers `F : E → ℝ`, and node vapour masses `m` (initial) and `m'`
(final), external additions `s` and retirements `r`, all `V → ℝ`, related by

`m' = m + B F + s - r`,

where `B` is the signed incidence matrix: `B_{ve}` is `1` if `v` is the head of `e`, plus `-1` if
`v` is its tail (so a loop column is `0`). Let `m_a > 0` be the dry-air mass, the same at both ends
of the interval. Then the [humidity ratio](humidity-ratio.md) of the total vapour mass satisfies

`(∑_v m'_v) / m_a = (∑_v m_v) / m_a + (∑_v s_v - ∑_v r_v) / m_a`:

internal transfers cancel, and the total ratio changes only by external additions minus
retirements. A changing dry-air mass is not covered.
