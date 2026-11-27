# Ancestry proportions summing to one bound the individual f4 rank

Let `μ` be a measure on the set `J` of loci, let the individuals be `0, …, n` and the ancestral
populations `0, …, k`, and let `Q` (an `(n + 1) × (k + 1)` real array) and `F : {0, …, k} → J → ℝ`
satisfy `∑ l, Q i l = 1` for every individual `i` (no sign condition), with every frequency of the
[global-ancestry family](ancestry-freq-of.md) of `Q` and `F` square integrable for `μ`. Then for all
right populations `R 0, …, R r` of the family, individuals or ancestral populations, the
[qpWave matrix](../abba-baba-test-and-f-statistic-estimators/f4-matrix.md) with the individuals as
left populations and individual `0` as their reference, with entries `f4(i, 0; R j, R 0)` for
`1 ≤ i ≤ n` and `1 ≤ j ≤ r`, has rank at most `k`, one less than the number of ancestral
populations.
