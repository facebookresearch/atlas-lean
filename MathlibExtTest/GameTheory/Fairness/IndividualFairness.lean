/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.GameTheory.Fairness.IndividualFairness
import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.NormNum

set_option autoImplicit false

open scoped BigOperators

namespace MathlibExtTest.GameTheory.Fairness.IndividualFairness

open MathlibExt.GameTheory.Fairness.IndividualFairness

@[expose] public section

/-- The discrete two-point task metric on `Fin 2`: distance `0` on the
diagonal and `1` off the diagonal. -/
def d2 : Fin 2 → Fin 2 → ℝ := fun x y => if x = y then 0 else 1

/-- Total variation distance takes the value `1` on opposite point masses
and `0` on identical uniform distributions over `Fin 2`. -/
theorem t1_tvDist_values :
    tvDist (fun i : Fin 2 => if i = 0 then (1 : ℝ) else (0 : ℝ))
      (fun i : Fin 2 => if i = 0 then (0 : ℝ) else (1 : ℝ)) = 1
    ∧ tvDist (fun _ : Fin 2 => (1 / 2 : ℝ))
        (fun _ : Fin 2 => (1 / 2 : ℝ)) = 0 := by
  constructor
  · norm_num [tvDist, MathlibExt.Probability.MarkovMixing.tvDist, Fin.sum_univ_two]
  · norm_num [tvDist, MathlibExt.Probability.MarkovMixing.tvDist, Fin.sum_univ_two]

/-- The constant fair-coin classifier on `Fin 2` is individually fair for
the discrete metric. -/
theorem t2_const_fair :
    IsLipschitzFair d2 (fun _ _ : Fin 2 => (1 / 2 : ℝ)) := by
  apply isLipschitzFair_const
  intro x y
  simp only [d2]
  by_cases h : x = y <;> simp [h]

/-- The point-mass coupling between opposite corners of `Fin 2` is a
coupling of the corner distributions, with transport cost `1`. -/
theorem t3_coupling_cost :
    IsCoupling (fun i : Fin 2 => if i = 0 then (1 : ℝ) else (0 : ℝ))
      (fun i : Fin 2 => if i = 0 then (0 : ℝ) else (1 : ℝ))
      (fun x y : Fin 2 => if x = 0 ∧ y = 1 then (1 : ℝ) else (0 : ℝ))
    ∧ transportCost d2
        (fun x y : Fin 2 => if x = 0 ∧ y = 1 then (1 : ℝ) else (0 : ℝ))
        = 1 := by
  constructor
  · refine ⟨?_, ?_, ?_⟩
    · intro x y
      show 0 ≤ (if x = 0 ∧ y = 1 then (1 : ℝ) else (0 : ℝ))
      by_cases h : x = 0 ∧ y = 1 <;> simp [h]
    · rw [Fin.forall_fin_two]
      constructor
      · norm_num [Fin.sum_univ_two]
      · norm_num [Fin.sum_univ_two]
    · rw [Fin.forall_fin_two]
      constructor
      · norm_num [Fin.sum_univ_two]
      · norm_num [Fin.sum_univ_two]
  · norm_num [transportCost, d2, Fin.sum_univ_two]

/-- T4: the induced distribution of the constant fair-coin classifier is
the fair coin, and is a probability distribution. -/
theorem t4_inducedDist_const :
    inducedDist (fun _ _ : Fin 2 => (1 / 2 : ℝ))
        (fun i : Fin 2 => if i = 0 then (1 : ℝ) else 0)
      = (fun _ : Fin 2 => (1 / 2 : ℝ))
    ∧ IsDist (inducedDist (fun _ _ : Fin 2 => (1 / 2 : ℝ))
        (fun i : Fin 2 => if i = 0 then (1 : ℝ) else 0)) := by
  have hS : IsDist (fun i : Fin 2 => if i = 0 then (1 : ℝ) else 0) := by
    refine ⟨?_, ?_⟩
    · intro i
      by_cases h : i = 0 <;> simp [h]
    · norm_num [Fin.sum_univ_two]
  have hrows : ∀ _ : Fin 2, IsDist (fun _ : Fin 2 => (1 / 2 : ℝ)) := by
    intro _
    refine ⟨fun _ => by norm_num, ?_⟩
    norm_num [Fin.sum_univ_two]
  refine ⟨?_, inducedDist_isDist hS hrows⟩
  funext o
  simp [inducedDist]

/-- T5: the classifier-level earthmover bound, applied to the constant
fair-coin classifier and the two point masses. -/
theorem t5_classifier_earthmover :
    tvDist (inducedDist (fun _ _ : Fin 2 => (1 / 2 : ℝ))
        (fun i : Fin 2 => if i = 0 then (1 : ℝ) else 0))
      (inducedDist (fun _ _ : Fin 2 => (1 / 2 : ℝ))
        (fun i : Fin 2 => if i = 0 then (0 : ℝ) else 1))
    ≤ earthmover d2 (fun i : Fin 2 => if i = 0 then (1 : ℝ) else 0)
        (fun i : Fin 2 => if i = 0 then (0 : ℝ) else 1) := by
  have hS : IsDist (fun i : Fin 2 => if i = 0 then (1 : ℝ) else 0) := by
    refine ⟨?_, ?_⟩
    · intro i
      by_cases h : i = 0 <;> simp [h]
    · norm_num [Fin.sum_univ_two]
  have hT : IsDist (fun i : Fin 2 => if i = 0 then (0 : ℝ) else 1) := by
    refine ⟨?_, ?_⟩
    · intro i
      by_cases h : i = 0 <;> simp [h]
    · norm_num [Fin.sum_univ_two]
  exact tvDist_inducedDist_le_earthmover t2_const_fair hS hT

end

end MathlibExtTest.GameTheory.Fairness.IndividualFairness
