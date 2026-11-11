/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.PopulationGenetics.SocialSelection.Hamilton
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

@[expose] public section

open MathlibExt.Biology.PopulationGenetics.SocialSelection
open scoped BigOperators

namespace MathlibExtTest.Biology.PopulationGenetics.SocialSelection.Hamilton

/-! ### A four-individual population

Own traits `z = (0, 0, 1, 1)` and partner traits `y = (0, 1, 1, 1)`: `z̄ = 1/2`, `ȳ = 3/4`,
`Var(z) = 1/4`, `Cov(y, z) = 1/8`, so regression relatedness is `r = 1/2`. -/

/-- Own trait values. -/
noncomputable def z : Fin 4 → ℝ := ![0, 0, 1, 1]

/-- Partner trait values. -/
noncomputable def y : Fin 4 → ℝ := ![0, 1, 1, 1]

theorem popCov_z_z : popCov z z = 1 / 4 := by
  simp [popCov_eq_expect_mul_sub, Fintype.expect_eq_sum_div_card, Fin.sum_univ_four, z]
  norm_num

theorem popCov_y_z : popCov y z = 1 / 8 := by
  simp [popCov_eq_expect_mul_sub, Fintype.expect_eq_sum_div_card, Fin.sum_univ_four, y, z]
  norm_num

theorem relatedness_y_z : relatedness y z = 1 / 2 := by
  rw [relatedness, popCov_y_z, popCov_z_z]
  norm_num

theorem popCov_zero_left (x : Fin 4 → ℝ) : popCov 0 x = 0 := by
  simp [popCov]

theorem transmission_self {n : ℕ} (w x : Fin n → ℝ) : transmission w x x = 0 := by
  simp [transmission]

/-! ### Smoke test: additive fitness, `r b > c`, the trait increases

`w = 1 + 4 y - z = (1, 5, 4, 4)`, i.e. `b = 4`, `c = 1`, zero residual, faithful transmission.
`r b = 2 > 1 = c`, and indeed `Δz̄ = 8 / 14 - 1/2 = 1/14 > 0`. -/

/-- Additive fitness with `α = 1`, `b = 4`, `c = 1`, `e = 0`. -/
noncomputable def wAdd : Fin 4 → ℝ := additiveFitness 1 4 1 y z 0

theorem wAdd_eq : wAdd = additiveFitness 1 4 1 y z 0 := rfl

theorem expect_wAdd : 𝔼 i, wAdd i = 7 / 2 := by
  simp [wAdd, additiveFitness, Fintype.expect_eq_sum_div_card, Fin.sum_univ_four, y, z]
  norm_num

example : 0 < meanTraitChange wAdd z z := by
  refine (hamilton_rule wAdd_eq ?_ ?_ (popCov_zero_left z) (transmission_self wAdd z)).mpr ?_
  · rw [expect_wAdd]; norm_num
  · rw [popCov_z_z]; norm_num
  · rw [relatedness_y_z]; norm_num

/-- The predicted increase matches the direct computation. -/
example : meanTraitChange wAdd z z = 1 / 14 := by
  simp [meanTraitChange, wAdd, additiveFitness, Fintype.expect_eq_sum_div_card,
    Fin.sum_univ_four, y, z]
  norm_num

/-- The identity `w̄ Δz̄ = Var(z) (r b - c) + Cov(e, z) + E[w (z' - z)]` on the example:
`7/2 · 1/14 = 1/4 · (2 - 1)`. -/
example : (𝔼 i, wAdd i) * meanTraitChange wAdd z z = 1 / 4 := by
  rw [price_hamilton wAdd_eq (sum_ne_zero_of_expect_pos (by rw [expect_wAdd]; norm_num))
      (by rw [popCov_z_z]; norm_num),
    popCov_z_z, relatedness_y_z, popCov_zero_left, transmission_self]
  norm_num

/-! ### Boundary case: zero trait variance

A monomorphic population `z₀ = (1, 1, 1, 1)` with the same additive fitness form (`b = 4`,
`c = 1`). `Var(z₀) = 0`, so relatedness is `0` by convention. `hamilton_rule_neg` without its
hypothesis `Var(z) ≠ 0` would claim a decrease (`r b - c = -1` under `r := 0`), but `Δz̄ = 0`:
there is no selection. The last example proves the hypothesis cannot be dropped. -/

/-- A monomorphic trait. -/
noncomputable def z₀ : Fin 4 → ℝ := fun _ => 1

theorem popCov_z₀_z₀ : popCov z₀ z₀ = 0 := by
  simp [popCov, z₀]

/-- Additive fitness on the monomorphic population. -/
noncomputable def w₀ : Fin 4 → ℝ := additiveFitness 1 4 1 y z₀ 0

theorem sum_w₀ : ∑ i, w₀ i = 12 := by
  simp [w₀, additiveFitness, Fin.sum_univ_four, y, z₀]
  norm_num

theorem meanTraitChange_w₀ : meanTraitChange w₀ z₀ z₀ = 0 := by
  have h := price_of_popCov_self_eq_zero (w := w₀) (z' := z₀) (by rw [sum_w₀]; norm_num)
    popCov_z₀_z₀
  rw [transmission_self] at h
  have hw : 𝔼 i, w₀ i ≠ 0 := by rw [Fintype.expect_eq_sum_div_card, sum_w₀]; norm_num
  exact (mul_eq_zero.mp h).resolve_left hw

example : relatedness y z₀ * 4 - 1 < 0 := by
  rw [relatedness_of_popCov_self_eq_zero popCov_z₀_z₀]
  norm_num

/-- The conclusion of `hamilton_rule_neg` fails at zero variance, although every other
hypothesis holds (additive fitness, `w̄ = 3 > 0`, zero residual, faithful transmission). -/
example : ¬ (meanTraitChange w₀ z₀ z₀ < 0 ↔ relatedness y z₀ * 4 < 1) := by
  rw [meanTraitChange_w₀, relatedness_of_popCov_self_eq_zero popCov_z₀_z₀]
  norm_num

/-! ### Boundary case: nonadditive fitness

Six individuals in which all four combinations of `z, y ∈ {0, 1}` occur:
`z = (0, 0, 0, 1, 1, 1)`, `y = (0, 0, 1, 0, 1, 1)`. Then `Var(z) = 1/4`, `Cov(y, z) = 1/12` and
`r = 1/3`. Fitness has a synergy term, `w = 1 + 4 y - z - z y = (1, 1, 5, 0, 3, 3)`, and is not
of the form `α + b y - c z` for any `α, b, c` (`wN_not_additive`), because `z y` is not in the span
of `1, y, z` on this population. Reading off the mechanistic coefficients `b = 4`, `c = 1` gives
`r b - c = 1/3 > 0`, yet the trait decreases: `Δz̄ = 6/13 - 1/2 = -1/26`. The residual
`e = -z y` has `Cov(e, z) = -1/6 ≠ 0`, so `hamilton_rule` does not apply. The exact criterion
`meanTraitChange_neg_iff` keeps the residual and still predicts the decrease:
`1/3 + (-1/6) / (1/4) = -1/3 < 0`.

In general, least-squares (partial regression) `b` and `c` always give `Cov(e, z) = 0`, so the
regression form of the rule stays exact for any fitness function; nonadditivity breaks the rule
only when `b` and `c` are mechanistic coefficients read off the model, as here. -/

/-- Own traits of the six-individual population. -/
noncomputable def zN : Fin 6 → ℝ := ![0, 0, 0, 1, 1, 1]

/-- Partner traits of the six-individual population. -/
noncomputable def yN : Fin 6 → ℝ := ![0, 0, 1, 0, 1, 1]

/-- The synergistic residual `-z y`. -/
noncomputable def eN : Fin 6 → ℝ := fun i => -(zN i * yN i)

/-- Nonadditive fitness `1 + 4 y - z - z y`. -/
noncomputable def wN : Fin 6 → ℝ := ![1, 1, 5, 0, 3, 3]

theorem wN_eq : wN = additiveFitness 1 4 1 yN zN eN := by
  funext i
  fin_cases i <;> norm_num [wN, additiveFitness, eN, yN, zN]

/-- `wN` has no additive representation with zero residual. -/
theorem wN_not_additive : ¬ ∃ α b c : ℝ, wN = additiveFitness α b c yN zN 0 := by
  rintro ⟨α, b, c, h⟩
  have h0 := congrFun h 0
  have h2 := congrFun h 2
  have h3 := congrFun h 3
  have h4 := congrFun h 4
  norm_num [wN, additiveFitness, yN, zN] at h0 h2 h3 h4
  linarith

theorem popCov_zN_zN : popCov zN zN = 1 / 4 := by
  simp [popCov_eq_expect_mul_sub, Fintype.expect_eq_sum_div_card, Fin.sum_univ_six, zN]
  norm_num

theorem popCov_yN_zN : popCov yN zN = 1 / 12 := by
  simp [popCov_eq_expect_mul_sub, Fintype.expect_eq_sum_div_card, Fin.sum_univ_six, yN, zN]
  norm_num

theorem relatedness_yN_zN : relatedness yN zN = 1 / 3 := by
  rw [relatedness, popCov_yN_zN, popCov_zN_zN]
  norm_num

theorem popCov_eN_zN : popCov eN zN = -1 / 6 := by
  simp [popCov_eq_expect_mul_sub, Fintype.expect_eq_sum_div_card, Fin.sum_univ_six, eN, yN, zN]
  norm_num

theorem expect_wN : 𝔼 i, wN i = 13 / 6 := by
  simp [wN, Fintype.expect_eq_sum_div_card, Fin.sum_univ_six]
  norm_num

example : 0 < relatedness yN zN * 4 - 1 := by
  rw [relatedness_yN_zN]; norm_num

example : meanTraitChange wN zN zN = -1 / 26 := by
  simp [meanTraitChange, wN, Fintype.expect_eq_sum_div_card, Fin.sum_univ_six, zN]
  norm_num

example : popCov eN zN ≠ 0 := by
  rw [popCov_eN_zN]; norm_num

/-- The rule read off the mechanistic coefficients mispredicts: its increase criterion holds but
the trait does not increase. -/
example : ¬ (0 < meanTraitChange wN zN zN ↔ 1 < relatedness yN zN * 4) := by
  have h : meanTraitChange wN zN zN = -1 / 26 := by
    simp [meanTraitChange, wN, Fintype.expect_eq_sum_div_card, Fin.sum_univ_six, zN]
    norm_num
  rw [h, relatedness_yN_zN]
  norm_num

example : meanTraitChange wN zN zN < 0 := by
  rw [meanTraitChange_neg_iff wN_eq (by rw [expect_wN]; norm_num)
    (by rw [popCov_zN_zN]; norm_num), relatedness_yN_zN, popCov_eN_zN, transmission_self,
    popCov_zN_zN]
  norm_num

/-! ### Boundary case: nonzero transmission term

Additive fitness `w = 1 + y - z = (1, 2, 1, 1)` (`b = c = 1`), so `r b - c = -1/2 < 0` and with
faithful transmission the trait would decrease. With a constant transmission bias `z' = z + 1/2`
the transmission term is `δ w̄ = 1/2 · 5/4 = 5/8`, which shifts the threshold to
`r b - c > -(5/8) / (1/4) = -5/2`; the criterion now predicts, and the population shows, an
increase: `w̄ Δz̄ = 1/4 · (-1/2) + 5/8 = 1/2`. -/

/-- Additive fitness with `b = c = 1`. -/
noncomputable def wT : Fin 4 → ℝ := additiveFitness 1 1 1 y z 0

/-- Biased transmission `z' = z + 1/2`. -/
noncomputable def zBias : Fin 4 → ℝ := fun i => z i + 1 / 2

theorem wT_eq : wT = additiveFitness 1 1 1 y z 0 := rfl

theorem expect_wT : 𝔼 i, wT i = 5 / 4 := by
  simp [wT, additiveFitness, Fintype.expect_eq_sum_div_card, Fin.sum_univ_four, y, z]
  norm_num

theorem transmission_wT : transmission wT z zBias = 5 / 8 := by
  rw [show zBias = fun i => z i + 1 / 2 from rfl, transmission_add_const, expect_wT]
  norm_num

example : relatedness y z * 1 - 1 < 0 := by
  rw [relatedness_y_z]; norm_num

/-- With faithful transmission the same fitness decreases the trait (`hamilton_rule_neg`). -/
example : meanTraitChange wT z z < 0 :=
  (hamilton_rule_neg wT_eq (by rw [expect_wT]; norm_num) (by rw [popCov_z_z]; norm_num)
    (popCov_zero_left z) (transmission_self wT z)).mpr (by rw [relatedness_y_z]; norm_num)

example : 0 < meanTraitChange wT z zBias := by
  rw [meanTraitChange_pos_iff wT_eq (by rw [expect_wT]; norm_num) (by rw [popCov_z_z]; norm_num),
    relatedness_y_z, popCov_zero_left, transmission_wT, popCov_z_z]
  norm_num

example : meanTraitChange wT z zBias = 2 / 5 := by
  simp [meanTraitChange, wT, zBias, additiveFitness, Fintype.expect_eq_sum_div_card,
    Fin.sum_univ_four, y, z]
  norm_num

/-- The robust rule on the smoke example: the residual and transmission terms vanish, so the
bound holds with `ε = 1/2`, and `r b - c = 1 > 1/2` forces an increase. -/
example : 0 < meanTraitChange wAdd z z :=
  meanTraitChange_pos_of_bound (ε := 1 / 2) wAdd_eq (by rw [expect_wAdd]; norm_num)
    (by rw [popCov_z_z]; norm_num)
    (by rw [popCov_zero_left, transmission_self, popCov_z_z]; norm_num)
    (by rw [relatedness_y_z]; norm_num)

end MathlibExtTest.Biology.PopulationGenetics.SocialSelection.Hamilton
