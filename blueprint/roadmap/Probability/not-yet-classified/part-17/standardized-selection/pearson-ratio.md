# Pearson Ratio

The totalized quotient `cov[f, g; μ] / (populationSD μ f * populationSD μ g)` (equal to `0`
by Lean's convention for division by zero when either variance is zero). When `μ` is a
probability measure, `f` and `g` are square-integrable, and both variances are positive, this is
the Pearson correlation of `f` and `g`.
