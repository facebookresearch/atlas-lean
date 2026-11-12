/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.FiniteProbability
public import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Ring

/-!
# The Hansen--Jagannathan bound

On a finite state space with physical probabilities `P`, let `m` be a stochastic discount
factor and `Rᵉ` an excess return priced at zero, `E_P[m * Rᵉ] = 0`. Cauchy--Schwarz applied
to the covariance gives the Hansen--Jagannathan bound: the Sharpe ratio of the excess
return is bounded by the SDF volatility over its mean,
`|E_P[Rᵉ]| / σ(Rᵉ) ≤ σ(m) / E_P[m]`, whenever the mean SDF is positive and the
excess-return variance is nonzero.

`expectation`, `variance`, and `covariance` are the canonical finite-probability ones
from `MathlibExt.Probability.FiniteProbability`; the covariance Cauchy--Schwarz step is
`FiniteProbability.covariance_sq_le_variance_mul_variance` in that file. The bound itself
is the finance-specific specialization.

## Main results

* `hansenJagannathan_bound`: the Hansen--Jagannathan bound.

## References

* L. P. Hansen and R. Jagannathan, *Implications of security market data for models of
  dynamic economies*, Journal of Political Economy 99 (1991), 225--262.
* J. H. Cochrane, *Asset Pricing*, revised edition, Princeton University Press (2005),
  Section 1.2 and Chapter 5.
-/

@[expose] public section

namespace MathlibExt.Probability.Finance.HansenJagannathanBound

open MathlibExt.Probability.FiniteProbability

/-- **Hansen--Jagannathan bound.** If the excess return is priced at zero by the SDF
(`E_P[m * Rᵉ] = 0`), the mean SDF is positive and the excess-return variance is nonzero, then
the Sharpe ratio of the excess return is bounded by the SDF volatility over its mean:
`|E_P[Rᵉ]| / σ(Rᵉ) ≤ σ(m) / E_P[m]`, with `σ` the square root of the variance and
`expectation` / `variance` the canonical finite-probability ones. -/
theorem hansenJagannathan_bound {Ω : Type*} [Fintype Ω] {P m Re : Ω → ℝ}
    (hP : ∀ ω, 0 < P ω) (hP1 : ∑ ω, P ω = 1)
    (hprice : expectation P (fun ω => m ω * Re ω) = 0) (hEm : 0 < expectation P m)
    (hVar : 0 < variance P Re) :
    |expectation P Re| / Real.sqrt (variance P Re)
      ≤ Real.sqrt (variance P m) / expectation P m := by
  have hPnonneg : ∀ ω, 0 ≤ P ω := fun ω => le_of_lt (hP ω)
  have hCov := covariance_eq_sub (p := P) hP1 m Re
  rw [hprice] at hCov
  have hCov2 : (covariance P m Re) ^ 2
      = (expectation P m * expectation P Re) ^ 2 := by rw [hCov]; ring
  have hCS : (covariance P m Re) ^ 2 ≤ variance P m * variance P Re :=
    covariance_sq_le_variance_mul_variance (p := P) (X := m) (Y := Re) hPnonneg
  rw [hCov2] at hCS
  have hVm : 0 ≤ variance P m := by
    unfold variance
    change 0 ≤ (∑ x, P x * ((m x - expectation P m) ^ 2))
    apply Finset.sum_nonneg
    intro ω _
    exact mul_nonneg (hPnonneg ω) (sq_nonneg _)
  have hsqrtRe : 0 < Real.sqrt (variance P Re) := Real.sqrt_pos.mpr hVar
  rw [div_le_div_iff₀ hsqrtRe hEm]
  have hsq : (|expectation P Re| * expectation P m) ^ 2
      ≤ (Real.sqrt (variance P m) * Real.sqrt (variance P Re)) ^ 2 := by
    rw [mul_pow, mul_pow, sq_abs, Real.sq_sqrt hVm, Real.sq_sqrt (le_of_lt hVar)]
    calc (expectation P Re) ^ 2 * (expectation P m) ^ 2
        = (expectation P m * expectation P Re) ^ 2 := by ring
      _ ≤ variance P m * variance P Re := hCS
  have hnn : 0 ≤ |expectation P Re| * expectation P m :=
    mul_nonneg (abs_nonneg _) (le_of_lt hEm)
  have hle := abs_le_of_sq_le_sq hsq (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  rw [abs_of_nonneg hnn] at hle
  exact hle

end MathlibExt.Probability.Finance.HansenJagannathanBound
