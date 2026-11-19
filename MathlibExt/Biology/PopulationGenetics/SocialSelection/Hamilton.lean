/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.PopulationGenetics.Selection

import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Hamilton's rule from the Price equation

A finite population of individuals `i : ι`. Individual `i` has trait value (breeding value) `z i`,
fitness `w i` (number of offspring), mean offspring trait `z' i`, and a social partner whose trait
value is `y i`. In the additive social fitness model

  `w i = α + b * y i - c * z i + e i`,

`b` is the fitness benefit of a partner's trait, `c` the fitness cost of one's own trait, and `e`
the residual. Relatedness is the regression coefficient of partner trait on own trait,
`r = Cov(y, z) / Var(z)` (Queller 1992). With all moments taken as population (not sample)
moments, the Price equation `w̄ Δz̄ = Cov(w, z) + E[w (z' - z)]` becomes

  `w̄ Δz̄ = Var(z) (r b - c) + Cov(e, z) + E[w (z' - z)]`.

When `Var(z) ≠ 0`, `w̄ > 0`, the residual is uncorrelated with the trait (`Cov(e, z) = 0`,
e.g. `e` is a least-squares residual) and transmission is faithful (`E[w (z' - z)] = 0`), the
mean trait increases iff `r b > c` (Hamilton's rule), and decreases iff `r b < c`.

## Main definitions

* `popCov x y = 𝔼 i, (x i - x̄) (y i - ȳ)`: the population covariance, exactly the covariance
  term of `Selection.price`; `popCov z z` is the trait variance.
* `relatedness y z = popCov y z / popCov z z`: regression relatedness.
* `meanTraitChange w z z' = ∑ w z' / ∑ w - z̄`: the change `Δz̄` in mean trait.
* `transmission w z z' = 𝔼 i, w i (z' i - z i)`: the transmission term of the Price equation.
* `additiveFitness α b c y z e`: the additive social fitness `α + b y - c z + e`.

## Main results

* `price_eq`: `Selection.price` restated with these definitions (not reproved).
* `popCov_additiveFitness`: `Cov(w, z) = b Cov(y, z) - c Var(z) + Cov(e, z)`.
* `price_hamilton`: `w̄ Δz̄ = Var(z) (r b - c) + Cov(e, z) + E[w (z' - z)]` for `Var(z) ≠ 0`.
* `meanTraitChange_pos_iff`, `meanTraitChange_neg_iff`: the exact sign criterion
  `Δz̄ > 0 ↔ r b - c + (Cov(e, z) + E[w (z' - z)]) / Var(z) > 0` (and `< 0`).
* `hamilton_rule`, `hamilton_rule_neg`: with `Cov(e, z) = 0` and zero transmission term,
  `Δz̄ > 0 ↔ c < r b` and `Δz̄ < 0 ↔ r b < c`.
* `meanTraitChange_pos_of_bound`, `meanTraitChange_neg_of_bound`: robust version; if
  `|Cov(e, z) + E[w (z' - z)]| ≤ ε Var(z)` then `r b - c > ε` forces an increase and
  `r b - c < -ε` a decrease.
* `price_of_popCov_self_eq_zero`: with zero trait variance there is no selection,
  `w̄ Δz̄ = E[w (z' - z)]`, whatever `b` and `c`.
* `transmission_add_const`: a constant transmission bias `z' = z + δ` contributes `δ w̄`, shifting
  the threshold to `r b - c > -(Cov(e, z) + δ w̄) / Var(z)`.

## Source receipt

* Reused, not reproved: `MathlibExt.Biology.PopulationGenetics.Selection.price`
  (`MathlibExt/Biology/PopulationGenetics/Selection.lean`), the exact finite-population Price
  equation with population covariance `𝔼 i, (w i - w̄) (z i - z̄)`. Fisher's fundamental theorem
  (`Selection.meanFitness_select_sub`) is not used.
* Reuse search (2026-11-11): no Hamilton's rule, kin-selection or regression-relatedness API in
  Mathlib or `MathlibExt` (`StatisticalGenetics/Relatedness.lean` is genomic relatedness, a
  different notion). The finite covariances found (`MendelianRandomization.weightedCov`,
  `CoalescentFStatistics.genCov`, `FStatisticsCovariance.centredCov`) are weighted,
  random-variable or measure-theoretic and sit behind probability imports, so `popCov` is
  defined here to match the covariance term of `Selection.price` syntactically.
* Mathematics: the regression form of Hamilton's rule from the Price equation follows
  Queller (1992) and Gardner, West & Wild (2011, §2); the rule itself is Hamilton (1964).

## References

* W. D. Hamilton, *The genetical evolution of social behaviour. I, II*, J. Theor. Biol. 7 (1964),
  1–52.
* G. R. Price, *Selection and covariance*, Nature 227 (1970), 520–521.
* D. C. Queller, *A general model for kin selection*, Evolution 46 (1992), 376–380.
* A. Gardner, S. A. West, G. Wild, *The genetical theory of kin selection*, J. Evol. Biol. 24
  (2011), 1020–1043.
-/

@[expose] public section

open Finset
open scoped BigOperators

namespace MathlibExt.Biology.PopulationGenetics.SocialSelection

variable {ι : Type*} [Fintype ι]

/-- The population covariance `𝔼 i, (x i - x̄) (y i - ȳ)` (population means, divisor `|ι|`). This
is the covariance term of `Selection.price`; `popCov z z` is the population variance of `z`. -/
noncomputable def popCov (x y : ι → ℝ) : ℝ := 𝔼 i, (x i - 𝔼 j, x j) * (y i - 𝔼 j, y j)

/-- Regression relatedness: the regression coefficient `Cov(y, z) / Var(z)` of partner trait `y`
on own trait `z` (Queller 1992). It is `0` when `Var(z) = 0`, by Lean's `a / 0 = 0`. -/
noncomputable def relatedness (y z : ι → ℝ) : ℝ := popCov y z / popCov z z

/-- The change `Δz̄ = ∑ i, w i z' i / ∑ i, w i - 𝔼 i, z i` in mean trait from parents to
offspring, for fitnesses `w`, parental traits `z` and mean offspring traits `z'`. -/
noncomputable def meanTraitChange (w z z' : ι → ℝ) : ℝ :=
  (∑ i, w i * z' i) / (∑ i, w i) - 𝔼 i, z i

/-- The transmission term `E[w (z' - z)] = 𝔼 i, w i (z' i - z i)` of the Price equation. -/
noncomputable def transmission (w z z' : ι → ℝ) : ℝ := 𝔼 i, w i * (z' i - z i)

/-- Additive social fitness `α + b y - c z + e`: baseline `α`, benefit `b` per unit of partner
trait `y`, cost `c` per unit of own trait `z`, residual `e`. -/
def additiveFitness (α b c : ℝ) (y z e : ι → ℝ) (i : ι) : ℝ := α + b * y i - c * z i + e i

/-- The Price equation `w̄ Δz̄ = Cov(w, z) + E[w (z' - z)]`, restated from `Selection.price`. -/
theorem price_eq (w z z' : ι → ℝ) (hw : ∑ i, w i ≠ 0) :
    (𝔼 i, w i) * meanTraitChange w z z' = popCov w z + transmission w z z' :=
  Selection.price w z z' hw

theorem popCov_self_nonneg (z : ι → ℝ) : 0 ≤ popCov z z :=
  expect_nonneg fun _ _ => mul_self_nonneg _

/-- `Cov(x, y) = 𝔼[x y] - x̄ ȳ`. -/
theorem popCov_eq_expect_mul_sub (x y : ι → ℝ) :
    popCov x y = (𝔼 i, x i * y i) - (𝔼 i, x i) * 𝔼 i, y i := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · simp [popCov]
  have hn : (Fintype.card ι : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  simp only [popCov, Fintype.expect_eq_sum_div_card]
  simp only [sub_mul, mul_sub, sum_sub_distrib, ← sum_mul, ← mul_sum, sum_const, card_univ,
    nsmul_eq_mul]
  field_simp
  ring

/-- Covariance of additive social fitness with the trait:
`Cov(α + b y - c z + e, z) = b Cov(y, z) - c Var(z) + Cov(e, z)`. -/
theorem popCov_additiveFitness (α b c : ℝ) (y z e : ι → ℝ) :
    popCov (additiveFitness α b c y z e) z = b * popCov y z - c * popCov z z + popCov e z := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · simp [popCov]
  have hn : (Fintype.card ι : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  simp only [popCov_eq_expect_mul_sub, additiveFitness, Fintype.expect_eq_sum_div_card]
  simp only [add_mul, sub_mul, sum_add_distrib, sum_sub_distrib, ← mul_sum, mul_assoc,
    sum_const, card_univ, nsmul_eq_mul]
  field_simp
  ring

theorem sum_ne_zero_of_expect_pos {w : ι → ℝ} (hw : 0 < 𝔼 i, w i) : ∑ i, w i ≠ 0 := by
  intro h
  rw [Fintype.expect_eq_sum_div_card, h, zero_div] at hw
  exact lt_irrefl 0 hw

/-- Hamilton's rule as an identity. In the additive model `w = α + b y - c z + e` with
`Var(z) ≠ 0`, `w̄ Δz̄ = Var(z) (r b - c) + Cov(e, z) + E[w (z' - z)]`. -/
theorem price_hamilton {w y z z' e : ι → ℝ} {α b c : ℝ} (hw : w = additiveFitness α b c y z e)
    (hsum : ∑ i, w i ≠ 0) (hV : popCov z z ≠ 0) :
    (𝔼 i, w i) * meanTraitChange w z z' =
      popCov z z * (relatedness y z * b - c) + popCov e z + transmission w z z' := by
  rw [price_eq w z z' hsum, hw, popCov_additiveFitness, relatedness]
  field_simp

/-- `w̄ Δz̄ = Var(z) (r b - c + (Cov(e, z) + E[w (z' - z)]) / Var(z))`. -/
theorem expect_mul_meanTraitChange {w y z z' e : ι → ℝ} {α b c : ℝ}
    (hw : w = additiveFitness α b c y z e) (hsum : ∑ i, w i ≠ 0) (hV : popCov z z ≠ 0) :
    (𝔼 i, w i) * meanTraitChange w z z' = popCov z z *
      (relatedness y z * b - c + (popCov e z + transmission w z z') / popCov z z) := by
  rw [price_hamilton hw hsum hV]
  field_simp
  ring

/-- The exact sign criterion for an increase. With additive fitness, `w̄ > 0` and `Var(z) ≠ 0`,
the mean trait increases iff `r b - c + (Cov(e, z) + E[w (z' - z)]) / Var(z) > 0`. -/
theorem meanTraitChange_pos_iff {w y z z' e : ι → ℝ} {α b c : ℝ}
    (hw : w = additiveFitness α b c y z e) (hw₀ : 0 < 𝔼 i, w i) (hV : popCov z z ≠ 0) :
    0 < meanTraitChange w z z' ↔
      0 < relatedness y z * b - c + (popCov e z + transmission w z z') / popCov z z := by
  have hV₀ : 0 < popCov z z := (popCov_self_nonneg z).lt_of_ne' hV
  have h := expect_mul_meanTraitChange (z' := z') hw (sum_ne_zero_of_expect_pos hw₀) hV
  rw [← mul_pos_iff_of_pos_left hw₀, h, mul_pos_iff_of_pos_left hV₀]

/-- The exact sign criterion for a decrease. -/
theorem meanTraitChange_neg_iff {w y z z' e : ι → ℝ} {α b c : ℝ}
    (hw : w = additiveFitness α b c y z e) (hw₀ : 0 < 𝔼 i, w i) (hV : popCov z z ≠ 0) :
    meanTraitChange w z z' < 0 ↔
      relatedness y z * b - c + (popCov e z + transmission w z z') / popCov z z < 0 := by
  have hV₀ : 0 < popCov z z := (popCov_self_nonneg z).lt_of_ne' hV
  have h := expect_mul_meanTraitChange (z' := z') hw (sum_ne_zero_of_expect_pos hw₀) hV
  constructor
  · intro hΔ
    by_contra hX
    rw [not_lt] at hX
    nlinarith [mul_neg_of_pos_of_neg hw₀ hΔ, mul_nonneg hV₀.le hX]
  · intro hX
    by_contra hΔ
    rw [not_lt] at hΔ
    nlinarith [mul_nonneg hw₀.le hΔ, mul_neg_of_pos_of_neg hV₀ hX]

/-- **Hamilton's rule.** In the additive social fitness model with positive mean fitness, nonzero
trait variance, a residual uncorrelated with the trait, and faithful transmission, the mean trait
increases iff `r b > c`. -/
theorem hamilton_rule {w y z z' e : ι → ℝ} {α b c : ℝ}
    (hw : w = additiveFitness α b c y z e) (hw₀ : 0 < 𝔼 i, w i) (hV : popCov z z ≠ 0)
    (he : popCov e z = 0) (hT : transmission w z z' = 0) :
    0 < meanTraitChange w z z' ↔ c < relatedness y z * b := by
  rw [meanTraitChange_pos_iff hw hw₀ hV, he, hT, zero_add, zero_div, add_zero, sub_pos]

/-- Hamilton's rule, decrease: under the same hypotheses, the mean trait decreases iff
`r b < c`. -/
theorem hamilton_rule_neg {w y z z' e : ι → ℝ} {α b c : ℝ}
    (hw : w = additiveFitness α b c y z e) (hw₀ : 0 < 𝔼 i, w i) (hV : popCov z z ≠ 0)
    (he : popCov e z = 0) (hT : transmission w z z' = 0) :
    meanTraitChange w z z' < 0 ↔ relatedness y z * b < c := by
  rw [meanTraitChange_neg_iff hw hw₀ hV, he, hT, zero_add, zero_div, add_zero, sub_neg]

/-- Robust Hamilton's rule, increase: if the residual and transmission terms are controlled by
`|Cov(e, z) + E[w (z' - z)]| ≤ ε Var(z)`, then `r b - c > ε` forces the mean trait to increase. -/
theorem meanTraitChange_pos_of_bound {w y z z' e : ι → ℝ} {α b c ε : ℝ}
    (hw : w = additiveFitness α b c y z e) (hw₀ : 0 < 𝔼 i, w i) (hV : popCov z z ≠ 0)
    (hbound : |popCov e z + transmission w z z'| ≤ ε * popCov z z)
    (hrule : ε < relatedness y z * b - c) : 0 < meanTraitChange w z z' := by
  have hV₀ : 0 < popCov z z := (popCov_self_nonneg z).lt_of_ne' hV
  rw [meanTraitChange_pos_iff hw hw₀ hV]
  have h : -ε ≤ (popCov e z + transmission w z z') / popCov z z := by
    rw [le_div_iff₀ hV₀]
    linarith [neg_abs_le (popCov e z + transmission w z z')]
  linarith

/-- Robust Hamilton's rule, decrease: under the same control, `r b - c < -ε` forces the mean
trait to decrease. -/
theorem meanTraitChange_neg_of_bound {w y z z' e : ι → ℝ} {α b c ε : ℝ}
    (hw : w = additiveFitness α b c y z e) (hw₀ : 0 < 𝔼 i, w i) (hV : popCov z z ≠ 0)
    (hbound : |popCov e z + transmission w z z'| ≤ ε * popCov z z)
    (hrule : relatedness y z * b - c < -ε) : meanTraitChange w z z' < 0 := by
  have hV₀ : 0 < popCov z z := (popCov_self_nonneg z).lt_of_ne' hV
  rw [meanTraitChange_neg_iff hw hw₀ hV]
  have h : (popCov e z + transmission w z z') / popCov z z ≤ ε := by
    rw [div_le_iff₀ hV₀]
    linarith [le_abs_self (popCov e z + transmission w z z')]
  linarith

/-- Zero trait variance makes the trait constant, so it covaries with nothing. -/
theorem popCov_eq_zero_of_popCov_self_eq_zero {z : ι → ℝ} (hV : popCov z z = 0) (x : ι → ℝ) :
    popCov x z = 0 := by
  have h := (expect_eq_zero_iff_of_nonneg (s := univ)
    (f := fun i => (z i - 𝔼 j, z j) * (z i - 𝔼 j, z j)) fun i _ => mul_self_nonneg _).mp hV
  refine expect_eq_zero fun i hi => ?_
  rw [mul_self_eq_zero.mp (h i hi), mul_zero]

/-- With zero trait variance there is no selection on the trait: `w̄ Δz̄ = E[w (z' - z)]` for any
fitness, additive or not, and any `b`, `c`. Regression relatedness is then `0` by convention, so
Hamilton's rule does not describe the response. -/
theorem price_of_popCov_self_eq_zero {w z z' : ι → ℝ} (hsum : ∑ i, w i ≠ 0)
    (hV : popCov z z = 0) :
    (𝔼 i, w i) * meanTraitChange w z z' = transmission w z z' := by
  rw [price_eq w z z' hsum, popCov_eq_zero_of_popCov_self_eq_zero hV, zero_add]

theorem relatedness_of_popCov_self_eq_zero {y z : ι → ℝ} (hV : popCov z z = 0) :
    relatedness y z = 0 := by
  rw [relatedness, hV, div_zero]

/-- A constant transmission bias `z' = z + δ` (e.g. biased mutation) gives transmission term
`δ w̄`. -/
theorem transmission_add_const (w z : ι → ℝ) (δ : ℝ) :
    transmission w z (fun i => z i + δ) = δ * 𝔼 i, w i := by
  simp only [transmission, add_sub_cancel_left, mul_expect]
  exact expect_congr rfl fun i _ => mul_comm _ _

end MathlibExt.Biology.PopulationGenetics.SocialSelection
