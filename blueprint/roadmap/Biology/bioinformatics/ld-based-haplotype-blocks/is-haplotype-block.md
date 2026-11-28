# Is Haplotype Block

The inclusive region from `i` to `j` is a Gabriel haplotype block at threshold `d` if
`i < j`, its outer pair is in strong LD, and `l / (l + r) ≥ d` over the reals, where `l` counts
strong-LD pairs and `r` counts strong-EHR pairs inside the region. The outer pair then ensures
`l + r > 0`.
