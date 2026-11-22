/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.Survival.KaplanMeier
public import Mathlib.Analysis.Complex.Exponential

/-!
# The Nelson–Aalen estimator and Greenwood's variance estimate

Right-censored survival data are grouped at `k` distinct observation times
`t₀ < t₁ < ⋯ < t_{k-1}` (`KaplanMeier.CensoredData`): at `tⱼ`, `dⱼ` subjects die and `Yⱼ`
subjects are at risk. The **Nelson–Aalen estimate** of the cumulative hazard is

  `Â(t) = ∑_{tⱼ ≤ t} dⱼ / Yⱼ`,

a right-continuous step function jumping by `dⱼ / Yⱼ` at `tⱼ`. **Greenwood's formula** estimates
the variance of the Kaplan–Meier estimate `Ŝ(t)` by

  `V̂(t) = Ŝ(t)² ∑_{tⱼ ≤ t} dⱼ / (Yⱼ (Yⱼ - dⱼ))`.

## Main results

* `nelsonAalen_nonneg`, `nelsonAalen_mono`: `Â` is a non-negative, non-decreasing function.
* `nelsonAalen_time`, `kmMass_eq_mul_nelsonAalen_jump`: the jump of `Â` at `tⱼ` is `dⱼ / Yⱼ`,
  and the Kaplan–Meier jump is `Ŝ(tⱼ₋)` times the Nelson–Aalen jump.
* `kmSurvival_le_exp_neg_nelsonAalen`: `Ŝ(t) ≤ exp (-Â(t))`, from `1 - x ≤ exp (-x)` factorwise.
* `greenwoodVariance_nonneg`.
* `greenwoodVariance_eq_textbook`: when `dⱼ < Yⱼ` at every `tⱼ ≤ t` (so every textbook
  denominator is positive), `V̂(t)` is the textbook sum over all `tⱼ ≤ t`.
* `greenwoodVariance_eq_totalizedSum`: in general, `V̂(t)` equals the Lean-totalized unfiltered
  sum, in which the excluded summands are `x / 0 = 0` by Lean's convention.
* `greenwoodVariance_eq_zero_of_deaths_eq_atRisk`: once everybody at risk has died,
  `Ŝ(t) = 0` and so `V̂(t) = 0`.

## Conventions

If `Yⱼ = 0` then also `dⱼ = 0` (`deaths_le_atRisk`), and `dⱼ / Yⱼ = 0` by Lean's convention
`x / 0 = 0`, matching the fact that no hazard is estimated where nobody is at risk. Greenwood's
summand is undefined when `dⱼ = Yⱼ`; `greenwoodVariance` sums only over `dⱼ < Yⱼ`.

## Scope

These are the finite-sample estimators only. Their large-sample theory (consistency, the
martingale central limit theorem, and that Greenwood's formula estimates the asymptotic variance
of `Ŝ(t)`) is not formalized here.

## References

* W. Nelson, *Theory and applications of hazard plotting for censored failure data*,
  Technometrics 14 (1972), 945–966.
* O. O. Aalen, *Nonparametric inference for a family of counting processes*, Ann. Statist. 6
  (1978), 701–726.
* M. Greenwood, *The natural duration of cancer*, Reports on Public Health and Medical Subjects
  33, HMSO, London (1926).
* J. D. Kalbfleisch and R. L. Prentice, *The Statistical Analysis of Failure Time Data*, 2nd ed.,
  Wiley (2002), Sections 1.4 and 4.2.
-/

@[expose] public section

set_option autoImplicit false

namespace MathlibExt.Probability.Statistics.KaplanMeier

open Finset

namespace CensoredData

variable {k : ℕ} (D : CensoredData k)

/-! ### The Nelson–Aalen estimator -/

/-- The **Nelson–Aalen estimate** `Â(t) = ∑_{tⱼ ≤ t} dⱼ / Yⱼ` of the cumulative hazard. A time
with nobody at risk (`Yⱼ = 0`, hence `dⱼ = 0`) contributes `0` by the convention `x / 0 = 0`. -/
noncomputable def nelsonAalen (t : ℝ) : ℝ := ∑ j with D.time j ≤ t, (D.deaths j : ℝ) / D.atRisk j

/-- The Nelson–Aalen estimate is non-negative. -/
theorem nelsonAalen_nonneg (t : ℝ) : 0 ≤ D.nelsonAalen t :=
  sum_nonneg fun _ _ => by positivity

/-- The Nelson–Aalen estimate is non-decreasing in `t`. -/
theorem nelsonAalen_mono : Monotone D.nelsonAalen := fun s t hst =>
  sum_le_sum_of_subset_of_nonneg
    (fun j hj => by
      simp only [mem_filter, mem_univ, true_and] at hj ⊢
      exact hj.trans hst)
    fun _ _ _ => by positivity

/-- At an observation time, `Â(tⱼ) = Â(tⱼ₋) + dⱼ / Yⱼ` with `Â(tⱼ₋) = ∑_{l < j} d_l / Y_l`. -/
theorem nelsonAalen_time (j : Fin k) :
    D.nelsonAalen (D.time j) =
      (∑ l with l < j, (D.deaths l : ℝ) / D.atRisk l) + (D.deaths j : ℝ) / D.atRisk j := by
  rw [nelsonAalen, show univ.filter (D.time · ≤ D.time j) = insert j (univ.filter (· < j)) by
      ext l; simp [D.strictMono_time.le_iff_le, le_iff_eq_or_lt],
    sum_insert (by simp), add_comm]

/-- The Kaplan–Meier jump at `tⱼ` is `Ŝ(tⱼ₋)` times the Nelson–Aalen jump `Â(tⱼ) - Â(tⱼ₋)`. -/
theorem kmMass_eq_mul_nelsonAalen_jump (j : Fin k) :
    D.kmMass j = (∏ l with l < j, D.kmFactor l) *
      (D.nelsonAalen (D.time j) - ∑ l with l < j, (D.deaths l : ℝ) / D.atRisk l) := by
  rw [D.nelsonAalen_time j, add_sub_cancel_left, kmMass]

/-- **Kaplan–Meier is below the exponentiated Nelson–Aalen estimate**: `Ŝ(t) ≤ exp (-Â(t))`,
since each factor satisfies `1 - dⱼ / Yⱼ ≤ exp (-dⱼ / Yⱼ)`. -/
theorem kmSurvival_le_exp_neg_nelsonAalen (t : ℝ) :
    D.kmSurvival t ≤ Real.exp (-D.nelsonAalen t) := by
  rw [nelsonAalen, ← sum_neg_distrib, Real.exp_sum, kmSurvival]
  refine Finset.prod_le_prod₀ (fun j _ => D.kmFactor_nonneg j) fun j _ => ?_
  have h := Real.add_one_le_exp (-((D.deaths j : ℝ) / D.atRisk j))
  rw [kmFactor]
  linarith

/-! ### Greenwood's variance estimate -/

/-- **Greenwood's variance estimate** of the Kaplan–Meier estimate at `t`:
`V̂(t) = Ŝ(t)² ∑_{tⱼ ≤ t, dⱼ < Yⱼ} dⱼ / (Yⱼ (Yⱼ - dⱼ))`.

This is Greenwood's plug-in *estimate* of the variance of `Ŝ(t)`, not the exact sampling variance
of the Kaplan–Meier estimator. Domain convention: the textbook summand is undefined when
`dⱼ = Yⱼ` (the Kaplan–Meier factor is `0`), so such times are explicitly excluded from the sum
rather than divided by zero. If no such time occurs by `t` the definition is the textbook formula
(`greenwoodVariance_eq_textbook`), and if
one occurs with `dⱼ > 0` at or before `t` then `Ŝ(t) = 0` and `V̂(t) = 0`
(`greenwoodVariance_eq_zero_of_deaths_eq_atRisk`). -/
noncomputable def greenwoodVariance (t : ℝ) : ℝ :=
  D.kmSurvival t ^ 2 * ∑ j with D.time j ≤ t ∧ D.deaths j < D.atRisk j,
    (D.deaths j : ℝ) / ((D.atRisk j : ℝ) * ((D.atRisk j : ℝ) - D.deaths j))

/-- Greenwood's variance estimate is non-negative. -/
theorem greenwoodVariance_nonneg (t : ℝ) : 0 ≤ D.greenwoodVariance t := by
  refine mul_nonneg (sq_nonneg _) (sum_nonneg fun j hj => ?_)
  have hlt : (D.deaths j : ℝ) < D.atRisk j := by exact_mod_cast (mem_filter.1 hj).2.2
  have : (0 : ℝ) ≤ D.atRisk j := Nat.cast_nonneg _
  exact div_nonneg (Nat.cast_nonneg _) (mul_nonneg this (by linarith))

/-- **Greenwood agrees with the textbook formula** when every textbook denominator is positive:
if `dⱼ < Yⱼ` at every `tⱼ ≤ t`, then `V̂(t) = Ŝ(t)² ∑_{tⱼ ≤ t} dⱼ / (Yⱼ (Yⱼ - dⱼ))`, a sum all of
whose denominators `Yⱼ (Yⱼ - dⱼ)` are positive. -/
theorem greenwoodVariance_eq_textbook {t : ℝ}
    (h : ∀ j, D.time j ≤ t → D.deaths j < D.atRisk j) :
    D.greenwoodVariance t = D.kmSurvival t ^ 2 * ∑ j with D.time j ≤ t,
      (D.deaths j : ℝ) / ((D.atRisk j : ℝ) * ((D.atRisk j : ℝ) - D.deaths j)) := by
  rw [greenwoodVariance]
  congr 1
  refine sum_congr ?_ fun _ _ => rfl
  ext j
  simp only [mem_filter, mem_univ, true_and]
  exact ⟨And.left, fun hj => ⟨hj, h j hj⟩⟩

/-- **Totalized form, no hypotheses.** `V̂(t)` equals the unfiltered sum over all `tⱼ ≤ t` *as a
Lean expression*: at an excluded time (`dⱼ = Yⱼ`) the textbook summand is undefined, and the Lean
term `dⱼ / (Yⱼ · 0)` is `0` only by the convention `x / 0 = 0`. This is an identity of totalized
expressions, not agreement with the textbook formula; for that see
`greenwoodVariance_eq_textbook`. -/
theorem greenwoodVariance_eq_totalizedSum (t : ℝ) :
    D.greenwoodVariance t = D.kmSurvival t ^ 2 * ∑ j with D.time j ≤ t,
      (D.deaths j : ℝ) / ((D.atRisk j : ℝ) * ((D.atRisk j : ℝ) - D.deaths j)) := by
  rw [greenwoodVariance, ← filter_filter, sum_filter (p := fun j => D.deaths j < D.atRisk j)]
  congr 1
  refine sum_congr rfl fun j _ => ?_
  split_ifs with h
  · rfl
  · have he : (D.deaths j : ℝ) = D.atRisk j := by
      exact_mod_cast le_antisymm (D.deaths_le_atRisk j) (not_lt.1 h)
    rw [he, sub_self, mul_zero, div_zero]

/-- If at some `tⱼ ≤ t` everybody at risk dies (`0 < dⱼ = Yⱼ`), then `Ŝ(t) = 0`. -/
theorem kmSurvival_eq_zero_of_deaths_eq_atRisk {t : ℝ} {j : Fin k} (hj : D.time j ≤ t)
    (hpos : 0 < D.deaths j) (heq : D.deaths j = D.atRisk j) : D.kmSurvival t = 0 := by
  refine prod_eq_zero (i := j) (by simp [hj]) ?_
  have hY : (D.atRisk j : ℝ) ≠ 0 := by exact_mod_cast (heq ▸ hpos).ne'
  rw [kmFactor, heq, div_self hY, sub_self]

/-- If at some `tⱼ ≤ t` everybody at risk dies (`0 < dⱼ = Yⱼ`), Greenwood's estimate is `0`. -/
theorem greenwoodVariance_eq_zero_of_deaths_eq_atRisk {t : ℝ} {j : Fin k} (hj : D.time j ≤ t)
    (hpos : 0 < D.deaths j) (heq : D.deaths j = D.atRisk j) : D.greenwoodVariance t = 0 := by
  rw [greenwoodVariance, D.kmSurvival_eq_zero_of_deaths_eq_atRisk hj hpos heq]
  simp

end CensoredData

end MathlibExt.Probability.Statistics.KaplanMeier
