/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Economics.Consumer.ExpenditureDuality
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

@[expose] public section

open Economics.Consumer

namespace MathlibExtTest.Economics.Consumer.ExpenditureDuality

/-! Two goods, consumption set `ℝ²₊`, prices `(1, 2)` and wealth `4`.

With utility `x₀ + x₁` the demand is `(4, 0)`, utility is locally nonsatiated, and the duality
gives `e(p, v(p, 4)) = 4`. With constant utility `0`, local nonsatiation fails and the cheapest
way to reach the indirect utility level `0` costs `0`, not `4`. -/



theorem demand1 : IsMarshallianDemand (fun x : Fin 2 → ℝ => x 0 + x 1)
    {x : Fin 2 → ℝ | 0 ≤ x} ![1, 2] 4 ![4, 0] := by
  constructor
  · constructor
    · show (0 : Fin 2 → ℝ) ≤ ![4, 0]
      intro i
      fin_cases i
      · show (0 : ℝ) ≤ 4
        norm_num
      · show (0 : ℝ) ≤ 0
        norm_num
    · show (![1, 2] : Fin 2 → ℝ) ⬝ᵥ ![4, 0] ≤ 4
      unfold dotProduct
      rw [Fin.sum_univ_two]
      simp [Matrix.cons_val_zero, Matrix.cons_val_one]
  · intro y hy
    obtain ⟨hyX, hcost⟩ := hy
    have h0 : (0 : ℝ) ≤ y 0 := hyX 0
    have h1 : (0 : ℝ) ≤ y 1 := hyX 1
    have hcost' : y 0 + 2 * y 1 ≤ 4 := by
      have hcost'' := hcost
      unfold dotProduct at hcost''
      rw [Fin.sum_univ_two] at hcost''
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, one_mul] at hcost''
      linarith
    show y 0 + y 1 ≤ (![4, 0] : Fin 2 → ℝ) 0 + (![4, 0] : Fin 2 → ℝ) 1
    have e0 : (![4, 0] : Fin 2 → ℝ) 0 = 4 := by simp
    have e1 : (![4, 0] : Fin 2 → ℝ) 1 = 0 := by simp
    rw [e0, e1]
    linarith

theorem lns1 : LocallyNonsatiated (fun x : Fin 2 → ℝ => x 0 + x 1)
    {x : Fin 2 → ℝ | 0 ≤ x} := by
  intro x hx ε hε
  refine ⟨fun i => x i + ε / 2, ?_, ?_, ?_⟩
  · show (0 : Fin 2 → ℝ) ≤ fun i => x i + ε / 2
    intro i
    have hi : (0 : ℝ) ≤ x i := hx i
    show (0 : ℝ) ≤ x i + ε / 2
    linarith
  · show dist (fun i => x i + ε / 2) x < ε
    have hle : dist (fun i => x i + ε / 2) x ≤ ε / 2 := by
      rw [dist_pi_le_iff (by linarith : (0 : ℝ) ≤ ε / 2)]
      intro i
      show dist (x i + ε / 2) (x i) ≤ ε / 2
      rw [Real.dist_eq]
      have heq : x i + ε / 2 - x i = ε / 2 := by ring
      rw [heq, abs_of_nonneg (by linarith : (0 : ℝ) ≤ ε / 2)]
    linarith
  · show x 0 + x 1 < x 0 + ε / 2 + (x 1 + ε / 2)
    linarith

theorem indirect1 : indirectUtility (fun x : Fin 2 → ℝ => x 0 + x 1)
    {x : Fin 2 → ℝ | 0 ≤ x} ![1, 2] 4 = 4 := by
  have h := indirectUtility_eq_of_isMarshallianDemand demand1
  simpa [Matrix.cons_val_zero, Matrix.cons_val_one] using h

theorem expend1 : expenditure (fun x : Fin 2 → ℝ => x 0 + x 1)
    {x : Fin 2 → ℝ | 0 ≤ x} ![1, 2]
    (indirectUtility (fun x : Fin 2 → ℝ => x 0 + x 1) {x : Fin 2 → ℝ | 0 ≤ x}
      ![1, 2] 4) = 4 :=
  expenditure_indirectUtility_eq lns1 demand1

theorem demand2 : IsMarshallianDemand (fun _ : Fin 2 → ℝ => (0 : ℝ))
    {x : Fin 2 → ℝ | 0 ≤ x} ![1, 2] 4 0 := by
  constructor
  · constructor
    · show (0 : Fin 2 → ℝ) ≤ 0
      exact le_refl _
    · show (![1, 2] : Fin 2 → ℝ) ⬝ᵥ (0 : Fin 2 → ℝ) ≤ 4
      have hz : (![1, 2] : Fin 2 → ℝ) ⬝ᵥ (0 : Fin 2 → ℝ) = 0 := by
        unfold dotProduct
        simp
      rw [hz]
      norm_num
  · intro y _
    show (0 : ℝ) ≤ 0
    exact le_refl _

theorem expend2 : expenditure (fun _ : Fin 2 → ℝ => (0 : ℝ))
    {x : Fin 2 → ℝ | 0 ≤ x} ![1, 2]
    (indirectUtility (fun _ : Fin 2 → ℝ => (0 : ℝ)) {x : Fin 2 → ℝ | 0 ≤ x}
      ![1, 2] 4) = 0 := by
  have hv : indirectUtility (fun _ : Fin 2 → ℝ => (0 : ℝ))
      {x : Fin 2 → ℝ | 0 ≤ x} ![1, 2] 4 = 0 := by
    have h := indirectUtility_eq_of_isMarshallianDemand demand2
    simpa using h
  rw [hv]
  unfold expenditure
  apply IsLeast.csInf_eq
  constructor
  · refine ⟨(0 : Fin 2 → ℝ), ⟨?_, ?_⟩, ?_⟩
    · show (0 : Fin 2 → ℝ) ≤ 0
      exact le_refl _
    · show (0 : ℝ) ≤ (fun _ : Fin 2 → ℝ => (0 : ℝ)) 0
      exact le_refl _
    · show (![1, 2] : Fin 2 → ℝ) ⬝ᵥ (0 : Fin 2 → ℝ) = 0
      unfold dotProduct
      simp
  · intro b hb
    obtain ⟨y, ⟨hyX, -⟩, rfl⟩ := hb
    show (0 : ℝ) ≤ (![1, 2] : Fin 2 → ℝ) ⬝ᵥ y
    have h0 : (0 : ℝ) ≤ y 0 := hyX 0
    have h1 : (0 : ℝ) ≤ y 1 := hyX 1
    have hcost : (![1, 2] : Fin 2 → ℝ) ⬝ᵥ y = y 0 + 2 * y 1 := by
      unfold dotProduct
      rw [Fin.sum_univ_two]
      simp [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [hcost]
    linarith

theorem notLNS : ¬ LocallyNonsatiated (fun _ : Fin 2 → ℝ => (0 : ℝ))
    {x : Fin 2 → ℝ | 0 ≤ x} := by
  intro h
  have h0mem : (0 : Fin 2 → ℝ) ∈ {x : Fin 2 → ℝ | 0 ≤ x} := by
    show (0 : Fin 2 → ℝ) ≤ 0
    exact le_refl _
  obtain ⟨y, -, -, hlt⟩ := h 0 h0mem 1 one_pos
  exact lt_irrefl _ hlt

end MathlibExtTest.Economics.Consumer.ExpenditureDuality
