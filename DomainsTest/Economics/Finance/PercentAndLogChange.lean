/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Domains.Economics.Finance.PercentAndLogChange

import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

@[expose] public section


namespace MathlibExtTest.Economics.Finance.PercentAndLogChange

open MathlibExt.Economics.Finance.Returns MathlibExt.Economics.Finance.PortfolioReturn
  MathlibExt.Economics.Finance.PercentAndLogChange

/-! ### Growth from `200` to `250` (every hypothesis holds) -/

theorem assetReturn_200_250 : assetReturn 200 250 = 1 / 4 := by
  norm_num [assetReturn]

/-- The growth factor is `1 + 1/4`. -/
theorem growth_factor_200_250 : grossReturn 200 250 = 1 + 1 / 4 := by
  rw [grossReturn_eq_one_add_assetReturn 250 (by norm_num), assetReturn_200_250]

/-- A base of `200` growing by `25%` can only end at `250`. -/
theorem level_of_quarter_growth (x₁ : ℝ) (h : assetReturn 200 x₁ = 1 / 4) : x₁ = 250 := by
  rw [← mul_one_add_assetReturn x₁ (by norm_num : (200 : ℝ) ≠ 0), h]
  norm_num

/-- The difference of logarithms is the logarithm of one plus the percentage change. -/
theorem log_sub_log_200_250 : Real.log 250 - Real.log 200 = Real.log (1 + 1 / 4) := by
  rw [← priceLogReturn_eq_log_sub_log (x₀ := 200) (x₁ := 250) (by norm_num) (by norm_num),
    priceLogReturn_eq_log_one_add_assetReturn, assetReturn_200_250]

/-- The percentage change is recovered from the difference of logarithms. -/
theorem assetReturn_from_logs_200_250 :
    (1 : ℝ) / 4 = Real.exp (Real.log 250 - Real.log 200) - 1 := by
  rw [← priceLogReturn_eq_log_sub_log (x₀ := 200) (x₁ := 250) (by norm_num) (by norm_num),
    ← assetReturn_eq_exp_priceLogReturn_sub_one (by norm_num) (by norm_num), assetReturn_200_250]

/-- The exact log change `log (5/4)` is strictly below the percentage change `1/4`. -/
theorem log_lt_quarter : Real.log (1 + 1 / 4) < 1 / 4 := by
  have h := priceLogReturn_lt_assetReturn (x₀ := 200) (x₁ := 250) (by norm_num) (by norm_num)
    (by norm_num)
  rwa [priceLogReturn_eq_log_one_add_assetReturn, assetReturn_200_250] at h

/-- The first-order error at `25%` growth is at most `(1/4)^2`. -/
theorem first_order_error_quarter : |Real.log (1 + 1 / 4) - 1 / 4| ≤ (1 / 4) ^ 2 := by
  have h := abs_priceLogReturn_sub_assetReturn_le (x₀ := 200) (x₁ := 250)
    (by rw [assetReturn_200_250, abs_of_pos (by norm_num)]; norm_num)
  rwa [priceLogReturn_eq_log_one_add_assetReturn, assetReturn_200_250] at h

/-! ### Two steps of `10%` and a doubling followed by a halving -/

/-- Two steps of `10%` compound to `21%`, not `20%`, while the log changes add exactly. -/
theorem two_ten_percent_steps :
    assetReturn 100 121 = 21 / 100 ∧
      assetReturn 100 121 ≠ assetReturn 100 110 + assetReturn 110 121 ∧
      priceLogReturn 100 121 = priceLogReturn 100 110 + priceLogReturn 110 121 := by
  have h1 : assetReturn 100 110 = 1 / 10 := by norm_num [assetReturn]
  have h2 : assetReturn 110 121 = 1 / 10 := by norm_num [assetReturn]
  have h := one_add_assetReturn_eq_mul (x₀ := (100 : ℝ)) (x₁ := 110) 121 (by norm_num)
    (by norm_num)
  rw [h1, h2] at h
  have h3 : assetReturn 100 121 = 21 / 100 := by linarith
  refine ⟨h3, ?_, priceLogReturn_add (by norm_num) (by norm_num) (by norm_num)⟩
  rw [h3, h1, h2]
  norm_num

/-- Doubling (`+100%`) then halving (`-50%`) returns to the start: the percentage changes do not
cancel, the log changes `log 2` and `-log 2` do. -/
theorem doubling_then_halving :
    assetReturn 100 200 + assetReturn 200 100 = 1 / 2 ∧
      priceLogReturn 100 200 = Real.log 2 ∧ priceLogReturn 200 100 = -Real.log 2 := by
  refine ⟨by norm_num [assetReturn], ?_, ?_⟩
  · rw [priceLogReturn_eq_log_one_add_assetReturn]
    norm_num [assetReturn]
  · rw [priceLogReturn_eq_log_one_add_assetReturn,
      show (1 : ℝ) + assetReturn 200 100 = 2⁻¹ by norm_num [assetReturn], Real.log_inv]

/-! ### Declines: above, at and below `-100%` -/

/-- A `60%` decline (`100 → 40`) is above `-100%`, and its log change `log (2/5)` is more
negative than `-3/5`. -/
theorem decline_sixty_percent : -1 < assetReturn 100 40 ∧ Real.log (2 / 5) < -3 / 5 := by
  refine ⟨(neg_one_lt_assetReturn_iff 40 (by norm_num)).mpr (by norm_num), ?_⟩
  have h := priceLogReturn_lt_assetReturn (x₀ := 100) (x₁ := 40) (by norm_num) (by norm_num)
    (by norm_num)
  rw [priceLogReturn_eq_log_one_add_assetReturn] at h
  norm_num [assetReturn] at h
  linarith

/-- A total loss (`100 → 0`) is not above `-100%`. Lean gives it the junk log change `0`, the
same as no change, and the inequality `priceLogReturn ≤ assetReturn` fails there: the later value
must be positive. -/
theorem total_loss_boundary :
    ¬ (-1 < assetReturn 100 0) ∧ priceLogReturn 100 0 = priceLogReturn 100 100 ∧
      ¬ (priceLogReturn 100 0 ≤ assetReturn 100 0) := by
  refine ⟨fun h => lt_irrefl (0 : ℝ) ((neg_one_lt_assetReturn_iff 0 (by norm_num)).mp h), ?_, ?_⟩
  · simp [priceLogReturn, logReturn, grossReturn]
  · simp [priceLogReturn, logReturn, grossReturn, assetReturn]

/-- A value below zero (`100 → -50`, a "change" of `-150%`) is not above `-100%`. Lean's log of
the negative ratio is that of its absolute value, so it reports the log change of a fall to `50`,
and the inequality `priceLogReturn ≤ assetReturn` fails. -/
theorem below_minus_hundred_boundary :
    ¬ (-1 < assetReturn 100 (-50)) ∧ priceLogReturn 100 (-50) = priceLogReturn 100 50 ∧
      ¬ (priceLogReturn 100 (-50) ≤ assetReturn 100 (-50)) := by
  have hj : priceLogReturn 100 (-50) = Real.log (1 / 2) := by
    simp only [priceLogReturn, logReturn, grossReturn]
    rw [show (-50 : ℝ) / 100 = -(1 / 2) by norm_num, Real.log_neg_eq_log]
  refine ⟨fun h => ?_, ?_, ?_⟩
  · have := (neg_one_lt_assetReturn_iff (-50) (by norm_num)).mp h
    norm_num at this
  · rw [hj]
    simp only [priceLogReturn, logReturn, grossReturn]
    norm_num
  · rw [hj, one_div, Real.log_inv]
    have h2 : Real.log 2 < 2 - 1 := Real.log_lt_sub_one_of_pos (by norm_num) (by norm_num)
    norm_num [assetReturn]
    linarith

/-! ### Zero base and zero intermediate value -/

/-- A zero base (`0 → 5`, e.g. a zero price-index base). Lean's percentage change is the junk
`0` ("no change"), so the growth-factor, level and log-difference identities fail and `-1 < 0`
does not make the later value positive: each `x₀ ≠ 0` or `0 < x₀` hypothesis is needed. The
exact identity with `log (1 + ·)` and the first-order bound still apply, with both sides the
junk value `0`. -/
theorem zero_base_boundary :
    assetReturn 0 5 = 0 ∧ grossReturn 0 5 ≠ 1 + assetReturn 0 5 ∧
      (0 : ℝ) * (1 + assetReturn 0 5) ≠ 5 ∧
      priceLogReturn 0 5 ≠ Real.log 5 - Real.log 0 ∧
      (-1 < assetReturn 0 (-5) ∧ ¬ (0 : ℝ) < -5) ∧
      priceLogReturn 0 5 = Real.log (1 + assetReturn 0 5) ∧
      |priceLogReturn 0 5 - assetReturn 0 5| ≤ assetReturn 0 5 ^ 2 := by
  have ha : assetReturn 0 5 = 0 := by simp [assetReturn]
  have hp : priceLogReturn 0 5 = 0 := by simp [priceLogReturn, logReturn, grossReturn]
  have h5 : Real.log 5 ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one (by norm_num) (by norm_num)
  refine ⟨ha, ?_, ?_, ?_, ⟨by simp [assetReturn], by norm_num⟩,
    priceLogReturn_eq_log_one_add_assetReturn 0 5,
    abs_priceLogReturn_sub_assetReturn_le (by rw [ha]; norm_num)⟩
  · simp [grossReturn, ha]
  · norm_num
  · rw [hp, Real.log_zero, sub_zero]
    exact h5.symm

/-- A zero intermediate value (`100 → 0 → 50`) breaks compounding: `x₁ ≠ 0` is needed. -/
theorem zero_intermediate_boundary :
    1 + assetReturn 100 50 ≠ (1 + assetReturn 100 0) * (1 + assetReturn 0 50) := by
  norm_num [assetReturn]

/-! ### No change, and a change outside the first-order range -/

/-- Without change the two measures agree (both `0`), so `x₁ ≠ x₀` is needed for the strict
inequality, and the weak inequality holds with equality. -/
theorem unchanged_equality :
    priceLogReturn 100 100 ≤ assetReturn 100 100 ∧
      priceLogReturn 100 100 = assetReturn 100 100 := by
  refine ⟨priceLogReturn_le_assetReturn (by norm_num) (by norm_num), ?_⟩
  simp [priceLogReturn, logReturn, grossReturn, assetReturn]

/-- At a `75%` decline (`100 → 25`) the error `2 log 2 - 3/4` exceeds `(3/4)^2`: the range
`|g| ≤ 1/2` of the first-order bound cannot be dropped. -/
theorem first_order_bound_range_needed :
    ¬ (|priceLogReturn 100 25 - assetReturn 100 25| ≤ assetReturn 100 25 ^ 2) := by
  have hle := priceLogReturn_le_assetReturn (x₀ := 100) (x₁ := 25) (by norm_num) (by norm_num)
  have ha : assetReturn 100 25 = -3 / 4 := by norm_num [assetReturn]
  have hp : priceLogReturn 100 25 = -(2 * Real.log 2) := by
    rw [priceLogReturn_eq_log_one_add_assetReturn, ha,
      show (1 : ℝ) + -3 / 4 = (2 ^ 2)⁻¹ by norm_num, Real.log_inv, Real.log_pow]
    push_cast
    ring
  rw [abs_of_nonpos (by linarith), ha, hp]
  have h2 := Real.log_two_gt_d9
  norm_num
  linarith

/-! ### Units -/

/-- Recording both values in persons (`2000 → 2100`) or both in thousands (`2 → 21/10`) gives the
same `5%` change and the same log change; mixing the units (`2 → 2100`) gives a `104900%`
change. -/
theorem units_boundary :
    assetReturn (1000 * 2) (1000 * (21 / 10)) = 1 / 20 ∧
      priceLogReturn (1000 * 2) (1000 * (21 / 10)) = priceLogReturn 2 (21 / 10) ∧
      assetReturn 2 2100 = 1049 := by
  refine ⟨?_, ?_, by norm_num [assetReturn]⟩
  · rw [assetReturn_mul_mul 2 (21 / 10) (by norm_num)]
    norm_num [assetReturn]
  · rw [priceLogReturn_eq_log_one_add_assetReturn, priceLogReturn_eq_log_one_add_assetReturn,
      assetReturn_mul_mul 2 (21 / 10) (by norm_num)]

/-! ### Two groups with unequal bases -/

/-- Groups of sizes `100` and `900` grow by `10%` and `0%`. The total (`1000 → 1010`) grows by
the base-weighted average `1%` of the group changes, not by their unweighted average `5%`, and its
exact log change is `log (1 + 1/100)`. -/
theorem two_groups_unequal_bases :
    assetReturn 1000 1010 =
        ∑ i : Fin 2, portfolioWeight 1 (![100, 900] i) 1000 *
          assetReturn (![100, 900] i) (![110, 900] i) ∧
      assetReturn 1000 1010 = 1 / 100 ∧
      (assetReturn 100 110 + assetReturn 900 900) / 2 = 1 / 20 ∧
      priceLogReturn 1000 1010 = Real.log (1 + 1 / 100) := by
  have hw := portfolioReturn_eq_weighted (s := (Finset.univ : Finset (Fin 2)))
    (h := fun _ => (1 : ℝ)) (P₀ := ![100, 900]) (P₁ := ![110, 900])
    (by intro i _; fin_cases i <;> norm_num) (by norm_num [Fin.sum_univ_two])
  have hT : (∑ j : Fin 2, (fun _ : Fin 2 => (1 : ℝ)) j * (![100, 900] : Fin 2 → ℝ) j) = 1000 := by
    norm_num [Fin.sum_univ_two]
  have hL : portfolioReturn (fun _ => (1 : ℝ)) ![100, 900] ![110, 900] Finset.univ =
      assetReturn 1000 1010 := by
    norm_num [portfolioReturn, assetReturn, Fin.sum_univ_two]
  have ha : assetReturn 1000 1010 = 1 / 100 := by norm_num [assetReturn]
  rw [hL, hT] at hw
  refine ⟨hw, ha, by norm_num [assetReturn], ?_⟩
  rw [priceLogReturn_eq_log_one_add_assetReturn, ha]

end MathlibExtTest.Economics.Finance.PercentAndLogChange

