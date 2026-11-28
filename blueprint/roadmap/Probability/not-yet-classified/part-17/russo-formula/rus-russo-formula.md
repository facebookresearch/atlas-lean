# Russo's formula

**Russo's formula**, covariance form: for every event `A` and `0 < p < 1`,
`d/dp ℙ_p(A) = (p (1 - p))⁻¹ (𝔼_p[N 1_A] - 𝔼_p[N] ℙ_p(A))`, with `N` the number of open
coordinates. No monotonicity is assumed. See also `StatMech.hasDerivAt_prob_eq_sum_pivotalProb`
(pivotal form, increasing `A`) and `StatMech.Sharpness.hasDerivAt_prob_eq_pivotalFactor`.

L. Russo, *A note on percolation*, 1978; G. Grimmett, *Percolation*, 1999, Section 2.4.
