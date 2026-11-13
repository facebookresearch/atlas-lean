# Hudson's F_ST (ratio of averages)

Hudson's `F_ST` over sites `s` in the ratio-of-averages form of Bhatia et al. (2013):
`∑ s, (p_A s - p_B s) ^ 2 / ∑ s, hudsonDen (p_A s) (p_B s)`. It is defined when the denominator
is positive (it vanishes only if every site is fixed for the same allele in both populations);
otherwise Lean's value `0` is a junk value.
