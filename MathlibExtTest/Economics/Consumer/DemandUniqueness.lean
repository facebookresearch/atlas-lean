/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Economics.Consumer.DemandUniqueness
public import MathlibExt.Economics.SecondWelfareTheorem
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases

@[expose] public section

open MathlibExt.Economics MathlibExt.Economics.Consumer
open MathlibExt.Economics.SecondWelfareTheorem (consumptionSet)

namespace MathlibExtTest.Economics.Consumer.DemandUniqueness

namespace UniquenessExamples

/-- Linear utility `x₀ + x₁` on two goods: quasiconcave but not strictly. -/
def linU (x : Fin 2 → ℝ) : ℝ := x 0 + x 1

theorem convex_consumptionSet_fin2 : Convex ℝ (consumptionSet (Fin 2)) := by
  intro x hx y hy a b ha hb hab
  simp only [consumptionSet, Set.mem_ofPred_eq] at hx hy ⊢
  intro l
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  exact add_nonneg (mul_nonneg ha (hx l)) (mul_nonneg hb (hy l))

/-- At prices `(1, 1)` and wealth `1`, two distinct bundles are demanded. -/
theorem linU_two_demanded :
    IsMarshallianDemand linU (consumptionSet (Fin 2)) ![1, 1] 1 ![1, 0] ∧
      IsMarshallianDemand linU (consumptionSet (Fin 2)) ![1, 1] 1 ![0, 1] ∧
      (![1, 0] : Fin 2 → ℝ) ≠ ![0, 1] := by
  have hdot : ∀ y : Fin 2 → ℝ, ![1, 1] ⬝ᵥ y = y 0 + y 1 := by
    intro y
    simp [dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  have hmem1 : (![1, 0] : Fin 2 → ℝ) ∈ budgetSet (consumptionSet (Fin 2)) ![1, 1] 1 := by
    simp only [budgetSet, consumptionSet, Set.mem_ofPred_eq]
    constructor
    · intro i
      fin_cases i <;> simp
    · rw [hdot]
      simp
  have hmem2 : (![0, 1] : Fin 2 → ℝ) ∈ budgetSet (consumptionSet (Fin 2)) ![1, 1] 1 := by
    simp only [budgetSet, consumptionSet, Set.mem_ofPred_eq]
    constructor
    · intro i
      fin_cases i <;> simp
    · rw [hdot]
      simp
  have hlin1 : linU ![1, 0] = 1 := by simp [linU]
  have hlin2 : linU ![0, 1] = 1 := by simp [linU]
  have hopt1 : ∀ y ∈ budgetSet (consumptionSet (Fin 2)) ![1, 1] 1, linU y ≤ linU ![1, 0] := by
    intro y hy
    simp only [budgetSet, consumptionSet, Set.mem_ofPred_eq] at hy
    obtain ⟨hyX, hyp⟩ := hy
    rw [hdot] at hyp
    rw [hlin1]
    simp only [linU]
    exact hyp
  have hopt2 : ∀ y ∈ budgetSet (consumptionSet (Fin 2)) ![1, 1] 1, linU y ≤ linU ![0, 1] := by
    intro y hy
    simp only [budgetSet, consumptionSet, Set.mem_ofPred_eq] at hy
    obtain ⟨hyX, hyp⟩ := hy
    rw [hdot] at hyp
    rw [hlin2]
    simp only [linU]
    exact hyp
  have hne : (![1, 0] : Fin 2 → ℝ) ≠ ![0, 1] := by
    intro h
    have h0 := congrFun h 0
    simp at h0
  exact ⟨⟨hmem1, hopt1⟩, ⟨hmem2, hopt2⟩, hne⟩

theorem linU_not_strictQuasiconcaveOn :
    ¬ StrictQuasiconcaveOn (budgetSet (consumptionSet (Fin 2)) ![1, 1] 1) linU := by
  intro h
  have hdot : ∀ y : Fin 2 → ℝ, ![1, 1] ⬝ᵥ y = y 0 + y 1 := by
    intro y
    simp [dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  have hmem1 : (![1, 0] : Fin 2 → ℝ) ∈ budgetSet (consumptionSet (Fin 2)) ![1, 1] 1 := by
    simp only [budgetSet, consumptionSet, Set.mem_ofPred_eq]
    constructor
    · intro i
      fin_cases i <;> simp
    · rw [hdot]
      simp
  have hmem2 : (![0, 1] : Fin 2 → ℝ) ∈ budgetSet (consumptionSet (Fin 2)) ![1, 1] 1 := by
    simp only [budgetSet, consumptionSet, Set.mem_ofPred_eq]
    constructor
    · intro i
      fin_cases i <;> simp
    · rw [hdot]
      simp
  have hne : (![1, 0] : Fin 2 → ℝ) ≠ ![0, 1] := by
    intro heq
    have h0 := congrFun heq 0
    simp at h0
  have hlt := h hmem1 hmem2 hne (by norm_num : (0:ℝ) < 1/2) (by norm_num : (0:ℝ) < 1/2)
    (by norm_num : (1/2:ℝ) + (1/2) = 1)
  have h1 : linU (![1, 0] : Fin 2 → ℝ) = 1 := by simp [linU]
  have h2 : linU (![0, 1] : Fin 2 → ℝ) = 1 := by simp [linU]
  have hmid : linU ((1/2:ℝ) • (![1, 0] : Fin 2 → ℝ) + (1/2:ℝ) • (![0, 1] : Fin 2 → ℝ)) = 1 := by
    simp [linU, Pi.add_apply, smul_eq_mul]
    ring
  rw [h1, h2, hmid] at hlt
  simp at hlt

/-- Square-root utility `√x₀ + √x₁`, strictly concave on the nonnegative orthant. -/
noncomputable def sqrtU (x : Fin 2 → ℝ) : ℝ := Real.sqrt (x 0) + Real.sqrt (x 1)

theorem sqrtU_strictConcaveOn :
    StrictConcaveOn ℝ (budgetSet (consumptionSet (Fin 2)) ![1, 1] 2) sqrtU := by
  constructor
  · exact convex_budgetSet convex_consumptionSet_fin2 _ _
  · intro x hx y hy hxy a b ha hb hab
    simp only [budgetSet, consumptionSet, Set.mem_ofPred_eq] at hx hy
    obtain ⟨hx0, hxp⟩ := hx
    obtain ⟨hy0, hyp⟩ := hy
    have hx0_mem0 : x 0 ∈ Set.Ici (0 : ℝ) := hx0 0
    have hy0_mem0 : y 0 ∈ Set.Ici (0 : ℝ) := hy0 0
    have hx0_mem1 : x 1 ∈ Set.Ici (0 : ℝ) := hx0 1
    have hy0_mem1 : y 1 ∈ Set.Ici (0 : ℝ) := hy0 1
    have hneq : x 0 ≠ y 0 ∨ x 1 ≠ y 1 := by
      by_contra h
      apply hxy
      funext i
      fin_cases i
      · by_contra h0
        exact h (Or.inl h0)
      · by_contra h1
        exact h (Or.inr h1)
    obtain ⟨hc_sqrt, hstrict_sqrt⟩ := Real.strictConcaveOn_sqrt
    have hconc_sqrt := Real.strictConcaveOn_sqrt.concaveOn
    obtain ⟨hc_sqrt2, hconc⟩ := hconc_sqrt
    have hLHS : a • sqrtU x + b • sqrtU y
        = (a * Real.sqrt (x 0) + b * Real.sqrt (y 0))
          + (a * Real.sqrt (x 1) + b * Real.sqrt (y 1)) := by
      simp only [sqrtU, smul_eq_mul]
      ring
    have hRHS : sqrtU (a • x + b • y)
        = Real.sqrt (a * x 0 + b * y 0) + Real.sqrt (a * x 1 + b * y 1) := by
      simp only [sqrtU, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rcases hneq with hne0 | hne1
    · have h0_lt : a * Real.sqrt (x 0) + b * Real.sqrt (y 0)
          < Real.sqrt (a * x 0 + b * y 0) := by
        have h := hstrict_sqrt hx0_mem0 hy0_mem0 hne0 ha hb hab
        simpa only [smul_eq_mul] using h
      have h1_le : a * Real.sqrt (x 1) + b * Real.sqrt (y 1)
          ≤ Real.sqrt (a * x 1 + b * y 1) := by
        have h := hconc hx0_mem1 hy0_mem1 ha.le hb.le hab
        simpa only [smul_eq_mul] using h
      rw [hLHS, hRHS]
      exact add_lt_add_of_lt_of_le h0_lt h1_le
    · have h1_lt : a * Real.sqrt (x 1) + b * Real.sqrt (y 1)
          < Real.sqrt (a * x 1 + b * y 1) := by
        have h := hstrict_sqrt hx0_mem1 hy0_mem1 hne1 ha hb hab
        simpa only [smul_eq_mul] using h
      have h0_le : a * Real.sqrt (x 0) + b * Real.sqrt (y 0)
          ≤ Real.sqrt (a * x 0 + b * y 0) := by
        have h := hconc hx0_mem0 hy0_mem0 ha.le hb.le hab
        simpa only [smul_eq_mul] using h
      rw [hLHS, hRHS]
      exact add_lt_add_of_le_of_lt h0_le h1_lt

theorem sqrtU_isMarshallianDemand :
    IsMarshallianDemand sqrtU (consumptionSet (Fin 2)) ![1, 1] 2 ![1, 1] := by
  have hdot : ∀ y : Fin 2 → ℝ, ![1, 1] ⬝ᵥ y = y 0 + y 1 := by
    intro y
    simp [dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  have hmem : (![1, 1] : Fin 2 → ℝ) ∈ budgetSet (consumptionSet (Fin 2)) ![1, 1] 2 := by
    simp only [budgetSet, consumptionSet, Set.mem_ofPred_eq]
    constructor
    · intro i
      fin_cases i <;> simp
    · rw [hdot]
      simp
      norm_num
  have hsqrt11 : sqrtU ![1, 1] = 2 := by
    simp [sqrtU, Real.sqrt_one]
    norm_num
  simp only [IsMarshallianDemand]
  constructor
  · exact hmem
  · intro y hy
    simp only [budgetSet, consumptionSet, Set.mem_ofPred_eq] at hy
    obtain ⟨hy0, hyp⟩ := hy
    rw [hdot] at hyp
    rw [hsqrt11]
    simp only [sqrtU]
    have h0 : (0:ℝ) ≤ y 0 := hy0 0
    have h1 : (0:ℝ) ≤ y 1 := hy0 1
    have hsq0 : (Real.sqrt (y 0))^2 = y 0 := Real.sq_sqrt h0
    have hsq1 : (Real.sqrt (y 1))^2 = y 1 := Real.sq_sqrt h1
    have hnn0 : (0:ℝ) ≤ Real.sqrt (y 0) := Real.sqrt_nonneg _
    have hnn1 : (0:ℝ) ≤ Real.sqrt (y 1) := Real.sqrt_nonneg _
    nlinarith [sq_nonneg (Real.sqrt (y 0) - Real.sqrt (y 1)),
      sq_nonneg (Real.sqrt (y 0) + Real.sqrt (y 1)),
      mul_nonneg hnn0 hnn1]

theorem sqrtU_demand_unique (x : Fin 2 → ℝ)
    (hx : IsMarshallianDemand sqrtU (consumptionSet (Fin 2)) ![1, 1] 2 x) : x = ![1, 1] := by
  exact eq_of_isMarshallianDemand convex_consumptionSet_fin2
    (strictQuasiconcaveOn_of_strictConcaveOn sqrtU_strictConcaveOn) hx
    sqrtU_isMarshallianDemand

end UniquenessExamples

end MathlibExtTest.Economics.Consumer.DemandUniqueness
