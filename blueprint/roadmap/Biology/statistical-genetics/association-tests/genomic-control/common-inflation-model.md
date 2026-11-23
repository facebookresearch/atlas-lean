# Common-inflation model of Gaussian null scores

Let `P` be a measure on a measurable space `Ω` and let `ι` be a type indexing markers. A
common-inflation model consists of

- an inflation factor `λ`, a nonnegative real number with `λ ≠ 0`, so `λ > 0`;
- for every marker `j`, a real function `Z_j` on `Ω`, its null score, with law `𝒩(0, λ)` under
  `P`.

Every score is thus assumed centred Gaussian with the same variance `λ`; the 1-df statistic of
marker `j` is `χ²_j = Z_j²`. Only the law of each score is assumed: the scores need not be
independent, and their joint law is not specified. With at least one marker, `P` is a
probability measure. The Gaussian laws are a distributional hypothesis, not derived from a
population-structure or sampling model; the calibration results for this model are
consequences of Gaussian rescaling and do not justify that hypothesis for association
statistics.
