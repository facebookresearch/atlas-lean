# X comm li kj of distinct

Valid commuting pair `(l,i)` vs `(k,j)` when `l≠j` and `i≠k`.
Both inequalities follow from `<` via `Nat.ne_of_lt` and `Ne.symm`;
order `i≠l` (`l≠j`) then `j≠k` (`i≠k`) as required by `x_comm`.
