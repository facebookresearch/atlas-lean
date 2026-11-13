# Sample Mean

The sample mean `x̄ = (∑ i, x i) / n` of data `x : ι → ℝ`, `n = card ι` (MF06.3). It is
ATLAS's finite-population mean `MathlibExt.Probability.Causality.popMean`, under the name used
by the sample statistics below (`sampleMean_eq_sum_div`), and it equals Mathlib's uniform
average `Finset.expect` over `univ` (`Fintype.expect_eq_sum_div_card`).
