/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Economics.SecondWelfareTheorem

/-! One consumer, two goods, `u z = z 0 + z 1`: the hypotheses of the second welfare theorem
hold at `x = (1, 1)`, which is supported by `p = (1, 1)`. At `p = (1, 0)`, `x = (0, 1)` (zero
wealth, no cheaper bundle) satisfies the quasi-equilibrium consumer condition but is not budget
optimal. -/

@[expose] public section

open MathlibExt.Economics.SecondWelfareTheorem

namespace MathlibExtTest.Economics.SecondWelfareTheorem

-- 1. Non-vacuity: hypotheses hold
theorem test_hcont :
    ∀ i : Fin 1,
      ContinuousOn ((fun _ : Fin 1 => fun z : Fin 2 → ℝ => z 0 + z 1) i)
        (consumptionSet (Fin 2)) := by
  intro i
  exact ((continuous_apply 0).add (continuous_apply 1)).continuousOn

theorem test_hqc : ∀ i : Fin 1,
    QuasiconcaveOn ℝ (consumptionSet (Fin 2))
      ((fun _ : Fin 1 => fun z : Fin 2 → ℝ => z 0 + z 1) i) := by
  intro i
  show QuasiconcaveOn ℝ (consumptionSet (Fin 2)) (fun z : Fin 2 → ℝ => z 0 + z 1)
  rw [quasiconcaveOn_iff_min_le]
  constructor
  · -- Convexity of consumption set
    intro x hx y hy a b ha hb hab l
    have h1 : ((a • x + b • y : Fin 2 → ℝ)) l = a * x l + b * y l := by
      simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [h1]
    exact add_nonneg (mul_nonneg ha (hx l)) (mul_nonneg hb (hy l))
  · intro x hx y hy a b ha hb hab
    have h0 : ((a • x + b • y : Fin 2 → ℝ)) 0 = a * x 0 + b * y 0 := by
      simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have h1 : ((a • x + b • y : Fin 2 → ℝ)) 1 = a * x 1 + b * y 1 := by
      simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have hlin : ((a • x + b • y : Fin 2 → ℝ)) 0 + ((a • x + b • y : Fin 2 → ℝ)) 1
        = a * (x 0 + x 1) + b * (y 0 + y 1) := by
      rw [h0, h1]
      ring
    have hmin1 : min (x 0 + x 1) (y 0 + y 1) ≤ x 0 + x 1 := min_le_left _ _
    have hmin2 : min (x 0 + x 1) (y 0 + y 1) ≤ y 0 + y 1 := min_le_right _ _
    have hle : a * min (x 0 + x 1) (y 0 + y 1) + b * min (x 0 + x 1) (y 0 + y 1)
        ≤ a * (x 0 + x 1) + b * (y 0 + y 1) :=
      add_le_add (mul_le_mul_of_nonneg_left hmin1 ha) (mul_le_mul_of_nonneg_left hmin2 hb)
    have heq : a * min (x 0 + x 1) (y 0 + y 1) + b * min (x 0 + x 1) (y 0 + y 1)
        = min (x 0 + x 1) (y 0 + y 1) := by
      rw [← add_mul, hab, one_mul]
    rw [heq] at hle
    rw [hlin]
    exact hle

theorem test_hlns :
    ∀ i : Fin 1, LocallyNonsatiated ((fun _ : Fin 1 => fun z : Fin 2 → ℝ => z 0 + z 1) i) := by
  intro i z hzX ε hε
  show ∃ z' ∈ consumptionSet (Fin 2), dist z' z < ε ∧
    ((fun _ : Fin 1 => fun z : Fin 2 → ℝ => z 0 + z 1) i) z <
      ((fun _ : Fin 1 => fun z : Fin 2 → ℝ => z 0 + z 1) i) z'
  -- path y δ = z + δ • 1
  set y : ℝ → (Fin 2 → ℝ) := fun δ => z + δ • 1 with hy_def
  have hy_cont : Continuous y := by
    unfold y
    exact continuous_const.add (continuous_id.smul continuous_const)
  have hy0 : y 0 = z := by simp [y]
  obtain ⟨δ₁, hδ₁pos, hδ₁⟩ := (Metric.continuousAt_iff.mp hy_cont.continuousAt) ε hε
  set δstar : ℝ := min (δ₁ / 2) (ε / 2) with hδstar_def
  have hδstar_pos : (0 : ℝ) < δstar := lt_min_iff.mpr ⟨by linarith, by linarith⟩
  have hδstar_lt : dist δstar (0 : ℝ) < δ₁ := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hδstar_pos]
    have : δstar ≤ δ₁ / 2 := by rw [hδstar_def]; exact min_le_left _ _
    linarith
  have hdist : dist (y δstar) z < ε := by
    have := hδ₁ hδstar_lt
    rwa [hy0] at this
  have hy_pos : ∀ l, 0 ≤ (y δstar) l := by
    intro l
    have hyl : (y δstar) l = z l + δstar := by
      simp [y, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_one]
    rw [hyl]
    have hzl := hzX l
    linarith
  refine ⟨y δstar, hy_pos, hdist, ?_⟩
  show ((fun _ : Fin 1 => fun z : Fin 2 → ℝ => z 0 + z 1) i) z <
    ((fun _ : Fin 1 => fun z : Fin 2 → ℝ => z 0 + z 1) i) (y δstar)
  have h0 : (y δstar) 0 = z 0 + δstar := by
    simp [y, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_one]
  have h1 : (y δstar) 1 = z 1 + δstar := by
    simp [y, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_one]
  simp only
  rw [h0, h1]
  linarith

theorem test_pareto :
    IsParetoOptimal (fun _ : Fin 1 => fun z : Fin 2 → ℝ => z 0 + z 1) (![1, 1] : Fin 2 → ℝ)
      (fun _ : Fin 1 => ![1, 1]) := by
  constructor
  · constructor
    · intro i l
      fin_cases l
      · show (0 : ℝ) ≤ ![1, 1] 0
        simp
      · show (0 : ℝ) ≤ ![1, 1] 1
        simp
    · rw [Fin.sum_univ_one]
  · rintro ⟨y, ⟨_, hsum_y⟩, _, ⟨i, hlt⟩⟩
    have hi0 : i = 0 := Subsingleton.elim _ _
    have hy0 : y 0 = (![1, 1] : Fin 2 → ℝ) := by
      have := hsum_y
      rw [Fin.sum_univ_one] at this
      exact this
    subst hi0
    simp only at hlt
    rw [hy0] at hlt
    exact lt_irrefl _ hlt

-- Existence via the second welfare theorem (not by exhibiting p)
example : ∃ p : Fin 2 → ℝ, p ≠ 0 ∧ IsQuasiSupportingPrice
    (fun _ : Fin 1 => fun z : Fin 2 → ℝ => z 0 + z 1) p (fun _ : Fin 1 => ![1, 1]) :=
  exists_isQuasiSupportingPrice test_hcont test_hqc test_hlns test_pareto

-- 2. Directly: quasi-equilibrium with p = [1,1]
example : IsQuasiSupportingPrice
    (fun _ : Fin 1 => fun z : Fin 2 → ℝ => z 0 + z 1)
    (![1, 1] : Fin 2 → ℝ) (fun _ : Fin 1 => ![1, 1]) := by
  intro i z hzX hutil
  have hval_x : value (![1, 1] : Fin 2 → ℝ) ((fun _ : Fin 1 => (![1, 1] : Fin 2 → ℝ)) i) = 2 := by
    unfold value
    rw [Fin.sum_univ_two]
    simp
    norm_num
  have hval_z : value (![1, 1] : Fin 2 → ℝ) z = z 0 + z 1 := by
    unfold value
    rw [Fin.sum_univ_two]
    simp
  have hutil_x :
      ((fun _ : Fin 1 => fun z : Fin 2 → ℝ => z 0 + z 1) i)
        ((fun _ : Fin 1 => (![1, 1] : Fin 2 → ℝ)) i) = 2 := by
    simp
    norm_num
  have hutil_z : ((fun _ : Fin 1 => fun z : Fin 2 → ℝ => z 0 + z 1) i) z = z 0 + z 1 := rfl
  rw [hutil_x, hutil_z] at hutil
  rw [hval_x, hval_z]
  linarith

-- 2. Directly: equilibrium with p = [1,1]
example : IsBudgetOptimal
    (fun _ : Fin 1 => fun z : Fin 2 → ℝ => z 0 + z 1)
    (![1, 1] : Fin 2 → ℝ) (fun _ : Fin 1 => ![1, 1]) := by
  intro i z hzX hle
  have hval_x : value (![1, 1] : Fin 2 → ℝ) ((fun _ : Fin 1 => (![1, 1] : Fin 2 → ℝ)) i) = 2 := by
    unfold value
    rw [Fin.sum_univ_two]
    simp
    norm_num
  have hval_z : value (![1, 1] : Fin 2 → ℝ) z = z 0 + z 1 := by
    unfold value
    rw [Fin.sum_univ_two]
    simp
  have hutil_x :
      ((fun _ : Fin 1 => fun z : Fin 2 → ℝ => z 0 + z 1) i)
        ((fun _ : Fin 1 => (![1, 1] : Fin 2 → ℝ)) i) = 2 := by
    simp
    norm_num
  have hutil_z : ((fun _ : Fin 1 => fun z : Fin 2 → ℝ => z 0 + z 1) i) z = z 0 + z 1 := rfl
  rw [hval_x, hval_z] at hle
  rw [hutil_x, hutil_z]
  linarith

-- 3. Quasi is weaker: p = [1,0], x = [0,1]
example : IsQuasiSupportingPrice
    (fun _ : Fin 1 => fun z : Fin 2 → ℝ => z 0 + z 1)
    (![1, 0] : Fin 2 → ℝ) (fun _ : Fin 1 => ![0, 1])
    ∧ ¬ IsBudgetOptimal
    (fun _ : Fin 1 => fun z : Fin 2 → ℝ => z 0 + z 1)
    (![1, 0] : Fin 2 → ℝ) (fun _ : Fin 1 => ![0, 1]) := by
  constructor
  · -- Quasi holds: wealth 0, any preferred bundle costs ≥ 0 via z 0 ≥ 0
    intro i z hzX hutil
    have hval_x : value (![1, 0] : Fin 2 → ℝ) ((fun _ : Fin 1 => (![0, 1] : Fin 2 → ℝ)) i) = 0 := by
      unfold value
      rw [Fin.sum_univ_two]
      simp
    have hval_z : value (![1, 0] : Fin 2 → ℝ) z = z 0 := by
      unfold value
      rw [Fin.sum_univ_two]
      simp
    rw [hval_x, hval_z]
    exact hzX 0
  · -- Not equilibrium: z = [0,2] costs 0 but gives higher utility
    intro h
    have hz_mem : (![0, 2] : Fin 2 → ℝ) ∈ consumptionSet (Fin 2) := by
      intro l
      fin_cases l
      · show (0 : ℝ) ≤ ![0, 2] 0
        simp
      · show (0 : ℝ) ≤ ![0, 2] 1
        simp
    have hval_le : value (![1, 0] : Fin 2 → ℝ) (![0, 2] : Fin 2 → ℝ)
        ≤ value (![1, 0] : Fin 2 → ℝ) ((fun _ : Fin 1 => (![0, 1] : Fin 2 → ℝ)) 0) := by
      have h1 : value (![1, 0] : Fin 2 → ℝ) (![0, 2] : Fin 2 → ℝ) = 0 := by
        unfold value
        rw [Fin.sum_univ_two]
        simp
      have h2 : value (![1, 0] : Fin 2 → ℝ) ((fun _ : Fin 1 => (![0, 1] : Fin 2 → ℝ)) 0) = 0 := by
        unfold value
        rw [Fin.sum_univ_two]
        simp
      rw [h1, h2]
    have hle := h 0 (![0, 2] : Fin 2 → ℝ) hz_mem hval_le
    have hutil_vals :
        ((fun _ : Fin 1 => fun z : Fin 2 → ℝ => z 0 + z 1) 0) (![0, 2] : Fin 2 → ℝ) = 2
        ∧ ((fun _ : Fin 1 => fun z : Fin 2 → ℝ => z 0 + z 1) 0)
          ((fun _ : Fin 1 => (![0, 1] : Fin 2 → ℝ)) 0) = 1 := by
      constructor
      · simp
      · simp
    rw [hutil_vals.1, hutil_vals.2] at hle
    norm_num at hle

/-! Full predicates: `p = (1, 1)` makes `x = (1, 1)` a price quasi-equilibrium with transfers,
which `isEquilibriumWithTransfers_of_cheaper` upgrades to an equilibrium. Zero prices are
excluded from both predicates. -/

theorem test_coord_zero : (![1, 1] : Fin 2 → ℝ) 0 = 1 := by simp

theorem test_coord_one : (![1, 1] : Fin 2 → ℝ) 1 = 1 := by simp

theorem test_value_eq (z : Fin 2 → ℝ) :
    value ![1, 1] z = z 0 + z 1 := by
  simp [value, Fin.sum_univ_two]

theorem test_value_zero : value (![1, 1] : Fin 2 → ℝ) 0 = 0 := by
  simp [test_value_eq]

theorem test_value_alloc (i : Fin 1) :
    value (![1, 1] : Fin 2 → ℝ) ((fun _ : Fin 1 => ![1, 1]) i) = 2 := by
  rw [test_value_eq]
  show (![1, 1] : Fin 2 → ℝ) 0 + (![1, 1] : Fin 2 → ℝ) 1 = 2
  rw [test_coord_zero, test_coord_one]
  norm_num

theorem test_isQuasiEquilibriumWithTransfers :
    IsQuasiEquilibriumWithTransfers
      (fun _ : Fin 1 => fun z : Fin 2 → ℝ => z 0 + z 1)
      ![1, 1] ![1, 1] (fun _ : Fin 1 => ![1, 1]) := by
  refine ⟨?_, ?_, ?_⟩
  · intro h
    have h0 := congrFun h (0 : Fin 2)
    simp at h0
  · refine ⟨?_, ?_⟩
    · intro i l
      fin_cases l
      · show (0:ℝ) ≤ ![1, 1] 0
        rw [test_coord_zero]
        norm_num
      · show (0:ℝ) ≤ ![1, 1] 1
        rw [test_coord_one]
        norm_num
    · rw [Fin.sum_univ_one]
  · intro i z hzX hlt
    rw [test_value_alloc i, test_value_eq z]
    have hlt' : ((fun _ : Fin 1 => (![1, 1] : Fin 2 → ℝ)) i) 0
        + ((fun _ : Fin 1 => (![1, 1] : Fin 2 → ℝ)) i) 1 < z 0 + z 1 := hlt
    have h2 : ((fun _ : Fin 1 => (![1, 1] : Fin 2 → ℝ)) i) 0
        + ((fun _ : Fin 1 => (![1, 1] : Fin 2 → ℝ)) i) 1 = 2 := by
      show (![1, 1] : Fin 2 → ℝ) 0 + (![1, 1] : Fin 2 → ℝ) 1 = 2
      rw [test_coord_zero, test_coord_one]
      norm_num
    rw [h2] at hlt'
    linarith

theorem test_isEquilibriumWithTransfers :
    IsEquilibriumWithTransfers
      (fun _ : Fin 1 => fun z : Fin 2 → ℝ => z 0 + z 1)
      ![1, 1] ![1, 1] (fun _ : Fin 1 => ![1, 1]) := by
  refine isEquilibriumWithTransfers_of_cheaper ?_ test_isQuasiEquilibriumWithTransfers ?_
  · intro i
    show ContinuousOn (fun z : Fin 2 → ℝ => z 0 + z 1) (consumptionSet (Fin 2))
    exact ((continuous_apply (0 : Fin 2)).add (continuous_apply (1 : Fin 2))).continuousOn
  · intro i
    refine ⟨0, ?_, ?_⟩
    · intro l
      simp
    · rw [test_value_zero, test_value_alloc i]
      norm_num

theorem test_zero_price_excluded :
    ¬ IsQuasiEquilibriumWithTransfers
      (fun _ : Fin 1 => fun z : Fin 2 → ℝ => z 0 + z 1)
      ![1, 1] 0 (fun _ : Fin 1 => ![1, 1]) := by
  intro h
  obtain ⟨hpne, _, _⟩ := h
  exact hpne rfl

example : ¬ IsEquilibriumWithTransfers
    (fun _ : Fin 1 => fun z : Fin 2 → ℝ => z 0 + z 1)
    ![1, 1] 0 (fun _ : Fin 1 => ![1, 1]) := by
  intro h
  exact h.1 rfl

end MathlibExtTest.Economics.SecondWelfareTheorem
