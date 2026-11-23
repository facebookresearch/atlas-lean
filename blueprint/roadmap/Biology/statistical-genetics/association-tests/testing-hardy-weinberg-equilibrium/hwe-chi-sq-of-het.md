# Hwe Chi Sq Of Het

Pearson's statistic as a function of the heterozygote count `h`, given `N` and `nA`: the
fitted statistic `PearsonLimit.hweStat` of the genotype table
`(n_BB, n_AB, n_AA) = ((2N - nA - h) / 2, h, (nA - h) / 2)`, whose cell `i` counts the
individuals carrying `i` copies of `A`. For impossible counts (`h > nA` or `nA - h` odd) the
natural-number floor division and truncated subtraction give a meaningless value; those counts
have null probability `0`.
