# Pearson Ratio

The Pearson quotient `cov[f, g; μ] / (populationSD μ f * populationSD μ g)`. It is the
correlation of `f` and `g` when both variances are positive (and `0`, by Lean's convention for
division by zero, when either variance is zero).
