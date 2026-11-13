# The data Lindeberg condition from convergent first and second running means

If the
sample means converge and the running means of squares converge, then the centred data
satisfy the Lindeberg condition of `tendstoInDistribution_bootMean`; in fact the truncated sums
are eventually `0`, because `max_{i<n} |x i - x̄ₙ| = o(√n)`.
