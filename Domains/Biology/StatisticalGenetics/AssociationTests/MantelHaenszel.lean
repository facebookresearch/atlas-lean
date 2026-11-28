/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# The Mantel–Haenszel summary odds ratio

The Mantel–Haenszel estimator recovers a common odds ratio when every stratum satisfies
its cross-product identity and the sum of the denominator weights is positive.
-/

@[expose] public section

namespace WantedExt.Biology.StatisticalGenetics.MantelHaenszelWanted

/-- The Mantel–Haenszel summary odds ratio `R = ∑_k (A_k D_k / T_k) / ∑_k (B_k C_k / T_k)`, a
cross-product estimator of a common odds ratio (not a risk ratio: for one table with
`(A, B, C, D) = (4, 2, 1, 3)` it is `6`, while the risk ratio is `2`). It is meaningful when every
total `T_k` and the denominator `∑_k B_k C_k / T_k` are positive; a zero denominator gives `0` by
Lean's convention `x / 0 = 0`. -/
noncomputable def summaryOddsRatio {K : ℕ} (A B C D : Fin K → ℝ) : ℝ :=
  (∑ k, A k * D k / (A k + B k + C k + D k)) / ∑ k, B k * C k / (A k + B k + C k + D k)

/-- **`R` recovers a common odds ratio** (Mantel and Haenszel 1959, p. 736). For `K` strata with
real cells and positive totals `T_k`, if every stratum has `A_k D_k = ψ B_k C_k` for one `ψ` and
`∑_k B_k C_k / T_k > 0`, then `R = ψ`.

Source: Mantel and Haenszel (1959), p. 736. -/
public theorem summaryOddsRatio_eq_of_common {K : ℕ} (A B C D : Fin K → ℝ) (ψ : ℝ)
    (hT : ∀ k, 0 < A k + B k + C k + D k) (hψ : ∀ k, A k * D k = ψ * (B k * C k))
    (hpos : 0 < ∑ k, B k * C k / (A k + B k + C k + D k)) :
    summaryOddsRatio A B C D = ψ := by
  -- Positive totals are part of the statistical statement, not needed for this identity.
  have := hT
  unfold summaryOddsRatio
  apply (div_eq_iff hpos.ne').2
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by rw [hψ k, mul_div_assoc]

end WantedExt.Biology.StatisticalGenetics.MantelHaenszelWanted
