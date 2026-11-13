# LD-score regression

LD-score regression (Bulik-Sullivan et al. 2015): for a standardized genotype matrix
(`IsStandardized`, so that `ldCorr` is the sample correlation and `ldScore` the LD score) and
`N ≠ 0`, `𝔼[χ² j] = N h² / M * ℓ j + (1 - h²)`. The expected association statistic is affine in
the LD score, with slope `N h² / M` and intercept `1 - h²`. The proof uses only that column `j`
has sum of squares `N`; the rest of the standardization is what makes `ℓ j` an LD score.
