/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.FiniteConditioning
public import MathlibExt.Probability.FiniteProbability
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

@[expose] public section

open Finset

namespace MathlibExtTest.Probability.FiniteConditioning

open MathlibExt.Probability.FiniteConditioning MathlibExt.Probability.FiniteProbability

/-- Tower in `FiniteProbability` vocabulary. -/
example {α C : Type*} [Fintype α] [Fintype C] [DecidableEq C] {p : α → ℝ}
    (hp0 : ∀ x, 0 ≤ p x) (G : α → C) (Y : α → ℝ) :
    expectation p Y = expectation (cellMass p G) (cellMean p G Y) :=
  sum_mul_eq_sum_cellMass_mul_cellMean hp0 G Y

/-- Total variance in `FiniteProbability` vocabulary. -/
example {α C : Type*} [Fintype α] [Fintype C] [DecidableEq C] {p : α → ℝ}
    (hp0 : ∀ x, 0 ≤ p x) (G : α → C) (Y : α → ℝ) :
    variance p Y =
      expectation (cellMass p G) (cellVar p G Y) + variance (cellMass p G) (cellMean p G Y) :=
  sum_mul_sq_sub_eq_within_add_between hp0 G Y

/-! ### Nonlinear conditional mean -/

noncomputable def nonlinearWeight : Fin 3 × Bool → ℝ := fun _ => 1 / 6

noncomputable def nonlinearRegressor : Fin 3 → ℝ := ![-1, 0, 1]

noncomputable def nonlinearOutcome : Fin 3 × Bool → ℝ :=
  fun x => nonlinearRegressor x.1 ^ 2 + if x.2 then 1 else -1

theorem nonlinearWeight_nonneg : ∀ x, 0 ≤ nonlinearWeight x := fun _ => by
  norm_num [nonlinearWeight]

theorem nonlinear_cellMass (c : Fin 3) : cellMass nonlinearWeight Prod.fst c = 1 / 3 := by
  fin_cases c <;> simp only [cellMass, Finset.sum_filter] <;>
    simp [nonlinearWeight, Fintype.sum_prod_type, Fin.sum_univ_three] <;>
    norm_num

theorem nonlinear_cellMean (c : Fin 3) :
    cellMean nonlinearWeight Prod.fst nonlinearOutcome c = nonlinearRegressor c ^ 2 := by
  rw [cellMean, nonlinear_cellMass]
  fin_cases c <;> simp only [Finset.sum_filter] <;>
    simp [nonlinearWeight, nonlinearOutcome, nonlinearRegressor, Fintype.sum_prod_type] <;>
    norm_num

theorem nonlinear_cellVar (c : Fin 3) :
    cellVar nonlinearWeight Prod.fst nonlinearOutcome c = 1 := by
  rw [cellVar, nonlinear_cellMass, nonlinear_cellMean]
  fin_cases c <;> simp only [Finset.sum_filter] <;>
    simp [nonlinearWeight, nonlinearOutcome, nonlinearRegressor, Fintype.sum_prod_type] <;>
    norm_num

/-- The regressor has mean `0`, computed on the cell law (change of variables). -/
theorem nonlinear_regressor_mean :
    ∑ x, nonlinearWeight x * nonlinearRegressor x.1 = 0 := by
  rw [sum_mul_comp_eq_sum_cellMass_mul nonlinearWeight Prod.fst nonlinearRegressor]
  simp only [nonlinear_cellMass, Fin.sum_univ_three, nonlinearRegressor]
  norm_num

/-- Nonlinear conditional mean: the cell mean is `X ^ 2`, which is not affine in `X`; the
outcome is uncorrelated with `X` (so the best linear predictor is constant), yet the
conditional mean carries between-cell variance `2/9` of the total variance `11/9`. -/
theorem nonlinear_conditional_mean_total_variance :
    (∀ c, cellMean nonlinearWeight Prod.fst nonlinearOutcome c = nonlinearRegressor c ^ 2) ∧
    (¬ ∃ a b : ℝ, ∀ c, cellMean nonlinearWeight Prod.fst nonlinearOutcome c =
        a + b * nonlinearRegressor c) ∧
    (∑ x, nonlinearWeight x * (nonlinearRegressor x.1 - ∑ y, nonlinearWeight y *
        nonlinearRegressor y.1) * (nonlinearOutcome x - ∑ y, nonlinearWeight y *
        nonlinearOutcome y) = 0) ∧
    (∑ c, cellMass nonlinearWeight Prod.fst c *
        (cellMean nonlinearWeight Prod.fst nonlinearOutcome c -
          ∑ c', cellMass nonlinearWeight Prod.fst c' *
            cellMean nonlinearWeight Prod.fst nonlinearOutcome c') ^ 2 = 2 / 9) ∧
    (∑ x, nonlinearWeight x * (nonlinearOutcome x - ∑ y, nonlinearWeight y *
        nonlinearOutcome y) ^ 2 = 11 / 9) := by
  have hbetween : ∑ c, cellMass nonlinearWeight Prod.fst c *
        (cellMean nonlinearWeight Prod.fst nonlinearOutcome c -
          ∑ c', cellMass nonlinearWeight Prod.fst c' *
            cellMean nonlinearWeight Prod.fst nonlinearOutcome c') ^ 2 = 2 / 9 := by
    simp only [nonlinear_cellMass, nonlinear_cellMean, Fin.sum_univ_three, nonlinearRegressor]
    norm_num
  refine ⟨nonlinear_cellMean, ?_, ?_, hbetween, ?_⟩
  · rintro ⟨a, b, h⟩
    have h0 := h 0
    have h1 := h 1
    have h2 := h 2
    simp only [nonlinear_cellMean, nonlinearRegressor] at h0 h1 h2
    norm_num at h0 h1 h2
    linarith
  · simp [nonlinearWeight, nonlinearOutcome, nonlinearRegressor, Fintype.sum_prod_type,
      Fin.sum_univ_three]
    norm_num
  · rw [sum_mul_sq_sub_eq_within_add_between nonlinearWeight_nonneg Prod.fst, hbetween]
    simp only [nonlinear_cellMass, nonlinear_cellVar, Fin.sum_univ_three]
    norm_num

/-! ### A zero-mass stratum -/

noncomputable def nullCellWeight : Fin 3 → ℝ := ![1 / 2, 1 / 2, 0]

def nullCellMap : Fin 3 → Fin 2 := ![0, 0, 1]

noncomputable def nullCellOutcome : Fin 3 → ℝ := ![1, 3, 100]

theorem nullCellWeight_nonneg : ∀ x, 0 ≤ nullCellWeight x := fun x => by
  fin_cases x <;> norm_num [nullCellWeight]

theorem nullCell_cellMass (c : Fin 2) :
    cellMass nullCellWeight nullCellMap c = if c = 0 then 1 else 0 := by
  fin_cases c
  · simp only [cellMass, Finset.sum_filter]
    simp [nullCellWeight, nullCellMap, Fin.sum_univ_three]
    norm_num
  · simp only [cellMass, Finset.sum_filter]
    simp [nullCellWeight, nullCellMap, Fin.sum_univ_three]

/-- The null cell's weighted sum vanishes although the cell contains the outcome `100`. -/
theorem null_cell_weighted_sum_eq_zero :
    ∑ x ∈ univ.filter (fun x => nullCellMap x = 1), nullCellWeight x * nullCellOutcome x = 0 := by
  rw [← cellMass_mul_cellMean nullCellWeight_nonneg, nullCell_cellMass]
  simp

/-- Zero-mass stratum: cell `1` has mass `0` but contains a point with outcome `100`. Lean's
`x / 0 = 0` makes its cell mean `0`; the tower holds for every version of the conditional
mean that is correct on positive-mass cells (here the value `37` on the null cell), and the
total variance `1` is all within-cell. -/
theorem zero_mass_stratum :
    cellMass nullCellWeight nullCellMap 1 = 0 ∧
    cellMean nullCellWeight nullCellMap nullCellOutcome 1 = 0 ∧
    cellMean nullCellWeight nullCellMap nullCellOutcome 0 = 2 ∧
    ∑ x, nullCellWeight x * (![2, 37] : Fin 2 → ℝ) (nullCellMap x) = 2 ∧
    ∑ x, nullCellWeight x * (nullCellOutcome x - ∑ y, nullCellWeight y * nullCellOutcome y) ^ 2
      = 1 := by
  have hm1 : cellMass nullCellWeight nullCellMap 1 = 0 := by simp [nullCell_cellMass]
  have hmean0 : cellMean nullCellWeight nullCellMap nullCellOutcome 0 = 2 := by
    rw [cellMean, nullCell_cellMass]
    simp only [Finset.sum_filter]
    simp [nullCellWeight, nullCellMap, nullCellOutcome, Fin.sum_univ_three]
    norm_num
  have hmean1 : cellMean nullCellWeight nullCellMap nullCellOutcome 1 = 0 := by
    rw [cellMean, hm1, div_zero]
  have htower : ∑ x, nullCellWeight x * (![2, 37] : Fin 2 → ℝ) (nullCellMap x) =
      ∑ x, nullCellWeight x * nullCellOutcome x := by
    refine sum_mul_comp_eq_sum_mul_of_eq_cellMean nullCellWeight_nonneg nullCellMap
      nullCellOutcome _ fun c hc => ?_
    fin_cases c
    · simpa using hmean0.symm
    · exact absurd hm1 hc
  refine ⟨hm1, hmean1, hmean0, ?_, ?_⟩
  · rw [htower]
    simp [nullCellWeight, nullCellOutcome, Fin.sum_univ_three]
    norm_num
  · rw [sum_mul_sq_sub_eq_within_add_between nullCellWeight_nonneg nullCellMap]
    have hvar0 : cellVar nullCellWeight nullCellMap nullCellOutcome 0 = 1 := by
      rw [cellVar, hmean0, nullCell_cellMass]
      simp only [Finset.sum_filter]
      simp [nullCellWeight, nullCellMap, nullCellOutcome, Fin.sum_univ_three]
      norm_num
    simp only [Fin.sum_univ_two, nullCell_cellMass, hvar0, hmean0, hmean1]
    norm_num

/-- The nonnegativity hypothesis cannot be dropped: with signed weights `1, -1` on a single
cell, the cell mass is `0`, so the cell mean is `0`, and the tower identity fails. -/
theorem tower_fails_for_signed_weights :
    ∑ x : Fin 2, (![1, -1] : Fin 2 → ℝ) x *
        cellMean ![1, -1] (fun _ : Fin 2 => (0 : Fin 1)) ![1, 0] 0 ≠
      ∑ x : Fin 2, (![1, -1] : Fin 2 → ℝ) x * (![1, 0] : Fin 2 → ℝ) x := by
  simp [cellMean, cellMass, Fin.sum_univ_two]

/-! ### A concrete Simpson reversal -/

/-- Cell masses `P(T = t, Z = z)`: treated units (`t = 1`) sit mostly in stratum `z = 1`. -/
noncomputable def simpsonCellMass : Fin 2 → Fin 2 → ℝ := ![![2 / 5, 1 / 10], ![1 / 10, 2 / 5]]

/-- Success rates `P(S | T = t, Z = z)`; treatment is better in each stratum. -/
noncomputable def simpsonRate : Fin 2 → Fin 2 → ℝ := ![![4 / 5, 2 / 5], ![9 / 10, 1 / 2]]

/-- Joint weight on `(t, z, s)`. -/
noncomputable def simpsonWeight : Fin 2 × Fin 2 × Bool → ℝ := fun x =>
  simpsonCellMass x.1 x.2.1 * if x.2.2 then simpsonRate x.1 x.2.1 else 1 - simpsonRate x.1 x.2.1

noncomputable def simpsonOutcome : Fin 2 × Fin 2 × Bool → ℝ := fun x => if x.2.2 then 1 else 0

def simpsonCell : Fin 2 × Fin 2 × Bool → Fin 2 × Fin 2 := fun x => (x.1, x.2.1)

theorem simpsonWeight_nonneg : ∀ x, 0 ≤ simpsonWeight x := by
  rintro ⟨t, z, s⟩
  fin_cases t <;> fin_cases z <;> cases s <;> norm_num [simpsonWeight, simpsonCellMass, simpsonRate]

/-- The fixture is a probability weight: its four cell masses sum to `1`. -/
theorem simpson_sum_cellMass : ∑ c, cellMass simpsonWeight simpsonCell c = 1 := by
  rw [sum_cellMass]
  simp [simpsonWeight, simpsonCellMass, Fintype.sum_prod_type]
  ring

theorem simpson_fine_cellMean (t z : Fin 2) :
    cellMean simpsonWeight simpsonCell simpsonOutcome (t, z) = simpsonRate t z := by
  fin_cases t <;> fin_cases z <;> simp only [cellMass, cellMean, Finset.sum_filter] <;>
    simp [simpsonWeight, simpsonCell, simpsonOutcome, simpsonCellMass, simpsonRate,
      Fintype.sum_prod_type] <;>
    norm_num

/-- Simpson reversal: treatment has the higher success rate in each stratum, but the lower
aggregate rate (`0.58 < 0.72`), because the aggregate rate is the mass-weighted average of
the stratum rates (`cellMean_comp_cellMean`) and treated units sit in the harder stratum. -/
theorem simpson_reversal :
    (∀ z, cellMean simpsonWeight simpsonCell simpsonOutcome (0, z) <
        cellMean simpsonWeight simpsonCell simpsonOutcome (1, z)) ∧
    cellMean simpsonWeight (fun x => (simpsonCell x).1) simpsonOutcome 1 = 29 / 50 ∧
    cellMean simpsonWeight (fun x => (simpsonCell x).1) simpsonOutcome 0 = 18 / 25 ∧
    cellMean simpsonWeight (fun x => (simpsonCell x).1) simpsonOutcome 1 <
      cellMean simpsonWeight (fun x => (simpsonCell x).1) simpsonOutcome 0 := by
  have hagg : ∀ t, cellMean simpsonWeight (fun x => (simpsonCell x).1) simpsonOutcome t =
      cellMean simpsonWeight (fun x => (simpsonCell x).1)
        (fun x => simpsonRate x.1 x.2.1) t := by
    intro t
    rw [← cellMean_comp_cellMean simpsonWeight_nonneg simpsonCell Prod.fst simpsonOutcome t]
    congr 1
    funext x
    exact simpson_fine_cellMean x.1 x.2.1
  have h1 : cellMean simpsonWeight (fun x => (simpsonCell x).1) simpsonOutcome 1 = 29 / 50 := by
    rw [hagg]
    simp only [cellMass, cellMean, Finset.sum_filter]
    simp [simpsonWeight, simpsonCell, simpsonCellMass, simpsonRate, Fintype.sum_prod_type]
    norm_num
  have h0 : cellMean simpsonWeight (fun x => (simpsonCell x).1) simpsonOutcome 0 = 18 / 25 := by
    rw [hagg]
    simp only [cellMass, cellMean, Finset.sum_filter]
    simp [simpsonWeight, simpsonCell, simpsonCellMass, simpsonRate, Fintype.sum_prod_type]
    norm_num
  refine ⟨fun z => ?_, h1, h0, by rw [h1, h0]; norm_num⟩
  rw [simpson_fine_cellMean, simpson_fine_cellMean]
  fin_cases z <;> norm_num [simpsonRate]

end MathlibExtTest.Probability.FiniteConditioning
