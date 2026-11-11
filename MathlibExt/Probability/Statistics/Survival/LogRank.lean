/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The tied log-rank variance term

At one distinct event time of a two-sample survival comparison, `Y` subjects are at risk, `Y₁`
of them in group 1, and `d` of them fail. Conditionally on the margins, the number of group-1
failures is hypergeometric (draw `d` of the `Y` subjects without replacement, `Y₁` marked), with
variance

  `d Y₁ (Y - Y₁) (Y - d) / (Y² (Y - 1))`

(Mantel 1966). Summing these over the event times gives the log-rank variance with ties.

## Main results

* `tiedLogRankVarianceTerm_nonneg`: the term is non-negative when `Y₁ ≤ Y` and `d ≤ Y`.
* `tiedLogRankVarianceTerm_one`: with a single failure (`d = 1`) it is the Breslow (Cox
  information) summand `Y₁ (Y - Y₁) / Y²`, as in `CoxPartialLikelihood.breslowInformation`.
* `tiedLogRankVarianceTerm_eq_mul`, `tiedLogRankVarianceTerm_le`: with ties it is the Breslow
  contribution of the `d` tied events, `d Y₁ (Y - Y₁) / Y²`, shrunk by the finite-population
  factor `(Y - d) / (Y - 1) ≤ 1`.

For example, with `Y = 4`, `Y₁ = 2` and `d = 2` the tied variance is `1 / 3`, while the Breslow
information of the two tied events is `2 · (2 · 2 / 4²) = 1 / 2`.

## Scope

The term is defined by its closed form. That it is the variance of the hypergeometric law is not
proved here.

## References

* N. Mantel, *Evaluation of survival data and two new rank order statistics arising in its
  consideration*, Cancer Chemother. Rep. 50 (1966), 163–170.
* J. D. Kalbfleisch and R. L. Prentice, *The Statistical Analysis of Failure Time Data*, 2nd ed.,
  Wiley (2002), Section 7.2.
-/

@[expose] public section

set_option autoImplicit false

namespace MathlibExt.Probability.Statistics.LogRank

/-- The **tied log-rank variance term** `d Y₁ (Y - Y₁) (Y - d) / (Y² (Y - 1))` at one event time
with `Y` at risk, `Y₁` of them in group 1, and `d` failures. It is the conditional
(hypergeometric) variance of the number of group-1 failures given the margins (Mantel 1966); for
`Y ≤ 1` that number is deterministic and the term is `0`. All subtractions are taken in `ℝ`, so
under `Y₁ ≤ Y` and `d ≤ Y` they agree with the natural-number differences. -/
noncomputable def tiedLogRankVarianceTerm (Y Y₁ d : ℕ) : ℝ :=
  if Y ≤ 1 then 0 else
    (d : ℝ) * Y₁ * ((Y : ℝ) - Y₁) * ((Y : ℝ) - d) / ((Y : ℝ) ^ 2 * ((Y : ℝ) - 1))

/-- The tied log-rank variance term is non-negative when `Y₁ ≤ Y` and `d ≤ Y`. -/
theorem tiedLogRankVarianceTerm_nonneg {Y Y₁ d : ℕ} (h₁ : Y₁ ≤ Y) (hd : d ≤ Y) :
    0 ≤ tiedLogRankVarianceTerm Y Y₁ d := by
  unfold tiedLogRankVarianceTerm
  split_ifs with hY
  · exact le_rfl
  have h₁' : (Y₁ : ℝ) ≤ Y := by exact_mod_cast h₁
  have hd' : (d : ℝ) ≤ Y := by exact_mod_cast hd
  have hY' : (1 : ℝ) ≤ Y := by exact_mod_cast (by omega : 1 ≤ Y)
  refine div_nonneg (mul_nonneg (mul_nonneg (by positivity) ?_) ?_) (mul_nonneg ?_ ?_) <;>
    nlinarith

/-- With ties, the term is the Breslow contribution `d Y₁ (Y - Y₁) / Y²` of the `d` tied events
times the finite-population correction `(Y - d) / (Y - 1)`. -/
theorem tiedLogRankVarianceTerm_eq_mul {Y : ℕ} (hY : 1 < Y) (Y₁ d : ℕ) :
    tiedLogRankVarianceTerm Y Y₁ d =
      d * ((Y₁ : ℝ) * ((Y : ℝ) - Y₁) / (Y : ℝ) ^ 2) * (((Y : ℝ) - d) / ((Y : ℝ) - 1)) := by
  have hY0 : (Y : ℝ) ≠ 0 := by positivity
  have hY1 : (Y : ℝ) - 1 ≠ 0 := sub_ne_zero.2 (by exact_mod_cast hY.ne')
  unfold tiedLogRankVarianceTerm
  split_ifs with h
  · omega
  field_simp

/-- **A single failure gives the Breslow term**: for `d = 1` the tied log-rank variance term is
`Y₁ (Y - Y₁) / Y²`, the summand of the Cox information `breslowInformation` at one risk set. -/
theorem tiedLogRankVarianceTerm_one {Y : ℕ} (hY : 1 < Y) (Y₁ : ℕ) :
    tiedLogRankVarianceTerm Y Y₁ 1 = (Y₁ : ℝ) * ((Y : ℝ) - Y₁) / (Y : ℝ) ^ 2 := by
  have hY1 : (Y : ℝ) - 1 ≠ 0 := sub_ne_zero.2 (by exact_mod_cast hY.ne')
  rw [tiedLogRankVarianceTerm_eq_mul hY, Nat.cast_one, div_self hY1, one_mul, mul_one]

/-- With at least one failure, the tied variance is at most the Breslow contribution
`d Y₁ (Y - Y₁) / Y²` of the `d` tied events; Breslow's information overstates it under ties. -/
theorem tiedLogRankVarianceTerm_le {Y Y₁ d : ℕ} (h₁ : Y₁ ≤ Y) (hd1 : 1 ≤ d) :
    tiedLogRankVarianceTerm Y Y₁ d ≤ d * ((Y₁ : ℝ) * ((Y : ℝ) - Y₁) / (Y : ℝ) ^ 2) := by
  have hB : 0 ≤ (d : ℝ) * ((Y₁ : ℝ) * ((Y : ℝ) - Y₁) / (Y : ℝ) ^ 2) := by
    have : (Y₁ : ℝ) ≤ Y := by exact_mod_cast h₁
    have : 0 ≤ (Y : ℝ) - Y₁ := by linarith
    exact mul_nonneg (Nat.cast_nonneg _) (div_nonneg (mul_nonneg (Nat.cast_nonneg _) this)
      (sq_nonneg _))
  rcases Nat.lt_or_ge 1 Y with hY | hY
  · rw [tiedLogRankVarianceTerm_eq_mul hY]
    have hY' : (1 : ℝ) < Y := by exact_mod_cast hY
    have hf : ((Y : ℝ) - d) / ((Y : ℝ) - 1) ≤ 1 := by
      rw [div_le_one (by linarith)]
      have : (1 : ℝ) ≤ d := by exact_mod_cast hd1
      linarith
    exact mul_le_of_le_one_right hB hf
  · unfold tiedLogRankVarianceTerm
    split_ifs with h
    · exact hB
    · omega

end MathlibExt.Probability.Statistics.LogRank
