# Foster–Greer–Thorbecke measure of a population

The Foster–Greer–Thorbecke measure `FGT_α` of a finite population `s` with incomes `x` is the
population average of the individual contributions: `(1 / |s|) * ∑_{i ∈ s} c(x(i))`, where
`c(y) = ((z - y) / z) ^ α` if `y < z` and `c(y) = 0` otherwise. Outside `z > 0` and `α ≥ 0` each
contribution follows the conventions of the [individual contribution](fgt-term.md). It is `0` for an
empty population.
