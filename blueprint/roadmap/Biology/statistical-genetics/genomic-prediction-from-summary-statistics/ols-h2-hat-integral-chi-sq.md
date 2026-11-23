# LD-score regression identifies `h²` from the expected statistics

For a probability
measure, mean-zero effects and noise, a standardized genotype matrix whose LD scores are not all
equal, and `N, M ≠ 0`, the unweighted LD-score regression estimator applied to the expected
association statistics `𝔼[χ²_j]` returns `h²` (`LDScoreRegression.olsH2Hat_integral_chiSqStrat`,
from the LDSC identity `𝔼[χ²_j] = 1 + N h² ℓ_j / M - h²`).
