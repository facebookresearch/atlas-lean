# Target vector of f4 statistics against the right populations

Let `μ` be a measure on `Ω`, `p X : Ω → ℝ` the allele frequency of each population `X` (any real
functions), `T` a target population, `S 0, …, S k` sources and `R 0, …, R r` right populations. The
qpAdm target vector is the vector `b` of length `r` with entries `b j = f4(T, S 0; R j, R 0)` for
`1 ≤ j ≤ r`, where `f4` is the [f4 statistic](../patterson-s-f-statistics/f4.md). An entry whose
integrand is not integrable is `0`, by the convention of the f4 statistic; for square-integrable
frequencies every entry is a genuine integral.
