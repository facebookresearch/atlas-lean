/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# The Mantel–Haenszel summary chi-square and summary odds ratio

For `K` strata, stratum `k` is a 2 × 2 table with cells `A_k, B_k` (exposed, unexposed cases),
`C_k, D_k` (exposed, unexposed controls), margins `N₁ = A + B`, `N₂ = C + D`, `M₁ = A + C`,
`M₂ = B + D` and total `T`. With all margins fixed, under the null hypothesis of no association
between exposure and disease, `A_k` has the hypergeometric law with mean `E(A) = N₁ M₁ / T` and
variance `V(A) = N₁ N₂ M₁ M₂ / (T² (T - 1))`. These moments are already proved in
`MathlibExt.Probability.Distributions.Hypergeometric` (`sum_mul_hypergeometricReal` and
`sum_sq_sub_mean_mul_hypergeometricReal`, with population `T`, `M₁` marked items and `N₁` draws).
The conditional hypergeometric law given the margins is the two-class case of
`measureReal_caseCount_genotypeTotal` in
`Domains.Biology.StatisticalGenetics.AssociationTests.CochranArmitageFixedMargin`.

Recorded here are the remaining identities of Mantel and Haenszel: `A - E(A) = (A D - B C) / T` and
the single-table corrected chi-square; the summary statistic `(∑ A - ∑ E(A))² / ∑ V(A)`; and the
summary odds ratio `R = ∑ (A D / T) / ∑ (B C / T)` (which Mantel and Haenszel call the summary
relative risk, since the odds ratio approximates the relative risk for a rare disease), a weighted
average of the stratum odds ratios with weights `B C / T`, equal to the common odds ratio when the
strata share one, and equal to `1` exactly when `∑ A = ∑ E(A)`. Consistency of `R` under
sparse-stratum or large-stratum asymptotics is a later result and is not stated here.

Sources: N. Mantel and W. Haenszel, "Statistical aspects of the analysis of data from
retrospective studies of disease", J. Natl. Cancer Inst. 22 (1959) 719–748, pp. 734–736.
-/
module

public import Batteries.Util.ProofWanted
public import Domains.Biology.StatisticalGenetics.AssociationTests.MantelHaenszel
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.AbsoluteValue.Basic
public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Ring

@[expose] public section

namespace WantedExt.Biology.StatisticalGenetics.MantelHaenszelWanted

/-- The fixed-margin null expectation `E(A) = N₁ M₁ / T = (A + B)(A + C) / (A + B + C + D)` of the
exposed-case count of a 2 × 2 table. It is meaningful when the total `T` is positive; if `T = 0`,
Lean's convention `x / 0 = 0` makes the value `0`. -/
noncomputable def expectedCount (A B C D : ℝ) : ℝ :=
  (A + B) * (A + C) / (A + B + C + D)

/-- The fixed-margin null variance `V(A) = N₁ N₂ M₁ M₂ / (T² (T - 1))` of the exposed-case count of
a 2 × 2 table. It is meaningful when `T > 1`; if `T = 0` or `T = 1`, Lean's convention `x / 0 = 0`
makes the value `0`. -/
noncomputable def countVariance (A B C D : ℝ) : ℝ :=
  (A + B) * (C + D) * (A + C) * (B + D) /
    ((A + B + C + D) ^ 2 * (A + B + C + D - 1))

/-- The Mantel–Haenszel summary chi-square `(∑_k A_k - ∑_k E(A_k))² / ∑_k V(A_k)`, without the
continuity correction. It is meaningful when `∑_k V(A_k) > 0`; if that sum is `0`, Lean's convention
`x / 0 = 0` makes the value `0`. -/
noncomputable def summaryChiSquare {K : ℕ} (A B C D : Fin K → ℝ) : ℝ :=
  (∑ k, A k - ∑ k, expectedCount (A k) (B k) (C k) (D k)) ^ 2 /
    ∑ k, countVariance (A k) (B k) (C k) (D k)

/-- **Observed minus expected** (Mantel and Haenszel 1959, pp. 734 and 736). For a 2 × 2 table
with real cells `A, B, C, D` and positive total `T = A + B + C + D`,
`A - (A + B)(A + C) / T = (A D - B C) / T`.

Source: Mantel and Haenszel (1959), p. 736. -/
public theorem sub_expectedCount {A B C D : ℝ} (hT : 0 < A + B + C + D) :
    A - expectedCount A B C D = (A * D - B * C) / (A + B + C + D) := by
  rw [expectedCount, eq_div_iff hT.ne', sub_mul, div_mul_cancel₀ _ hT.ne']
  ring

/-- **Single-table corrected chi-square** (Mantel and Haenszel 1959, p. 734). For a 2 × 2 table
with real cells `A, B, C, D`, positive margins `A + B`, `C + D`, `A + C`, `B + D` and total
`T = A + B + C + D > 1`,
`(|A - E(A)| - 1/2)² / V(A) = (|A D - B C| - T/2)² (T - 1) / ((A + B)(C + D)(A + C)(B + D))`.

Source: Mantel and Haenszel (1959), p. 734. -/
public theorem_wanted correctedChiSquare_eq {A B C D : ℝ} (hN₁ : 0 < A + B) (hN₂ : 0 < C + D)
    (hM₁ : 0 < A + C) (hM₂ : 0 < B + D) (hT : 1 < A + B + C + D) :
    (|A - expectedCount A B C D| - 1 / 2) ^ 2 / countVariance A B C D =
      (|A * D - B * C| - (A + B + C + D) / 2) ^ 2 * (A + B + C + D - 1) /
        ((A + B) * (C + D) * (A + C) * (B + D))

/-- **`R` is a weighted average of stratum odds ratios** (Mantel and Haenszel 1959, p. 736). For
`K ≥ 1` strata with real cells, positive totals `T_k` and `B_k C_k > 0` for every `k`, `R` equals
`∑_k w_k (A_k D_k / (B_k C_k)) / ∑_k w_k` with weights `w_k = B_k C_k / T_k`.

Source: Mantel and Haenszel (1959), p. 736. -/
public theorem_wanted summaryOddsRatio_eq_weighted {K : ℕ} (hK : 0 < K) (A B C D : Fin K → ℝ)
    (hT : ∀ k, 0 < A k + B k + C k + D k) (hBC : ∀ k, 0 < B k * C k) :
    summaryOddsRatio A B C D =
      (∑ k, B k * C k / (A k + B k + C k + D k) * (A k * D k / (B k * C k))) /
        ∑ k, B k * C k / (A k + B k + C k + D k)

/-- **`R = 1` exactly when observed equals expected** (Mantel and Haenszel 1959, p. 736). For `K`
strata with real cells, positive totals `T_k` and `∑_k B_k C_k / T_k > 0`, `R = 1` if and only
if `∑_k A_k = ∑_k E(A_k)`.

Source: Mantel and Haenszel (1959), p. 736. -/
public theorem summaryOddsRatio_eq_one_iff {K : ℕ} (A B C D : Fin K → ℝ)
    (hT : ∀ k, 0 < A k + B k + C k + D k)
    (hpos : 0 < ∑ k, B k * C k / (A k + B k + C k + D k)) :
    summaryOddsRatio A B C D = 1 ↔
      ∑ k, A k = ∑ k, expectedCount (A k) (B k) (C k) (D k) := by
  -- By `sub_expectedCount`, `∑ A - ∑ E(A) = ∑ A D / T - ∑ B C / T`.
  have hdiff : ∑ k, A k - ∑ k, expectedCount (A k) (B k) (C k) (D k) =
      ∑ k, A k * D k / (A k + B k + C k + D k) -
        ∑ k, B k * C k / (A k + B k + C k + D k) := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun k _ => by rw [sub_expectedCount (hT k), sub_div]
  rw [summaryOddsRatio, div_eq_one_iff_eq hpos.ne', ← sub_eq_zero, ← hdiff, sub_eq_zero]

/-- **The summary chi-square vanishes exactly when `R = 1`** (Mantel and Haenszel 1959,
pp. 735–736). For `K` strata with real cells, positive totals `T_k`, `∑_k B_k C_k / T_k > 0` and
`∑_k V(A_k) > 0`, the uncorrected summary chi-square is `0` if and only if `R = 1`.

Source: Mantel and Haenszel (1959), pp. 735–736. -/
public theorem_wanted summaryChiSquare_eq_zero_iff {K : ℕ} (A B C D : Fin K → ℝ)
    (hT : ∀ k, 0 < A k + B k + C k + D k)
    (hpos : 0 < ∑ k, B k * C k / (A k + B k + C k + D k))
    (hV : 0 < ∑ k, countVariance (A k) (B k) (C k) (D k)) :
    summaryChiSquare A B C D = 0 ↔ summaryOddsRatio A B C D = 1

end WantedExt.Biology.StatisticalGenetics.MantelHaenszelWanted
