# X comm jl ik of distinct

Valid commuting pair `(j,l)` vs `(i,k)` when `j≠k` and `l≠i`.
Both inequalities follow from `<` via `Nat.ne_of_lt` and `Ne.symm`;
order `i≠l` (`j≠k`) then `j≠k` (`l≠i`) as required by `x_comm`.
