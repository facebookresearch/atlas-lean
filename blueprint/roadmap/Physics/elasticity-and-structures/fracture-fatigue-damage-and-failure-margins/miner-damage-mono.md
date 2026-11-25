# Monotonicity of the Miner sum for nonnegative counts

For a finite class type, counts $0 \le n_i \le n'_i$ and lives $0 < N'_i \le N_i$ for every class
$i$,

$$\sum_i \frac{n_i}{N_i} \le \sum_i \frac{n'_i}{N'_i}.$$

More declared cycles and shorter calibrated lives never decrease the [damage sum](miner-damage.md):
it accumulates as cycles are added, and a shorter-life (conservative) calibration gives a value at
least as large. The counts must be nonnegative: for a negative count a shorter life lowers the term.
