# Source matrix of f4 statistics against the right populations

Let `μ` be a measure on `Ω` and `p X : Ω → ℝ` the allele frequency of each population `X` (any real
functions). For sources `S 0, …, S k` and right populations `R 0, …, R r`, the qpAdm source matrix
is the real `r × k` matrix `A` with entries `A j l = f4(S l, S 0; R j, R 0)` for `1 ≤ j ≤ r` and
`1 ≤ l ≤ k`, where `f4` is the [f4 statistic](../patterson-s-f-statistics/f4.md): its rows belong to
the right populations other than the reference `R 0`, its columns to the sources other than the
reference source `S 0`. An entry whose integrand is not integrable is `0`, by the convention of the
f4 statistic; for square-integrable frequencies every entry is a genuine integral.
