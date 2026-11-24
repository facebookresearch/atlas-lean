# Miner Damage unit change

Unit convention. Counts and lives must use one cycle unit. Changing it by a factor `c > 0`
for both (cycles to reversals: `c = 2`) leaves `D` unchanged; converting only the counts
multiplies `D` by `c`, so counts in reversals read against lives in cycles double `D`. The second
identity shows that `D` scales linearly with a common factor on the counts,
with no cap at `D = 1`.
