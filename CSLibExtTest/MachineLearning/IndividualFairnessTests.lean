/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.MachineLearning.IndividualFairness
import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.NormNum

set_option autoImplicit false

open scoped BigOperators Matrix

namespace Cslib.MachineLearning.IndividualFairness

open MathlibExt.Probability.FiniteTransport
open MathlibExt.Probability.MarkovMixing (tvDist)

/-- The discrete two-point task metric on `Fin 2`: distance `0` on the
diagonal and `1` off the diagonal. -/
private def d2 : Fin 2 → Fin 2 → ℝ := fun x y => if x = y then 0 else 1

/-- The constant fair-coin classifier on `Fin 2` is individually fair for
the discrete metric. -/
private theorem t2_const_fair :
    IsLipschitzFair d2 (fun _ _ : Fin 2 => (1 / 2 : ℝ)) := by
  refine isLipschitzFair_const ?_ _ ?_
  · intro x y
    simp only [d2]
    by_cases h : x = y <;> simp [h]
  · refine ⟨fun _ => by norm_num, ?_⟩
    norm_num [Fin.sum_univ_two]

/-- T3: the rows of a fair classifier must be probability distributions: the constant
classifier with entries `-1` has total variation distance `0` between any two rows, yet it is
not individually fair. -/
private theorem t3_not_fair_of_negative_rows :
    ¬ IsLipschitzFair d2 (fun _ _ : Fin 2 => (-1 : ℝ)) := by
  intro h
  have h0 := (h.1 0).1 0
  norm_num at h0

/-- The `0` point mass on `Fin 2`, as a probability-distribution subtype
element. -/
private def delta0D : {p : Fin 2 → ℝ // IsDist p} :=
  ⟨fun i => if i = 0 then (1 : ℝ) else 0, by
    refine ⟨?_, ?_⟩
    · intro i
      by_cases h : i = 0 <;> simp [h]
    · norm_num [Fin.sum_univ_two]⟩

/-- The `1` point mass on `Fin 2`, as a probability-distribution subtype
element. -/
private def delta1D : {p : Fin 2 → ℝ // IsDist p} :=
  ⟨fun i => if i = 0 then (0 : ℝ) else 1, by
    refine ⟨?_, ?_⟩
    · intro i
      by_cases h : i = 0 <;> simp [h]
    · norm_num [Fin.sum_univ_two]⟩

/-- T4: the induced distribution of the constant fair-coin classifier is
the fair coin, and is a probability distribution. -/
private theorem t4_vecMul_const :
    (fun i : Fin 2 => if i = 0 then (1 : ℝ) else 0)
        ᵥ* Matrix.of (fun _ _ : Fin 2 => (1 / 2 : ℝ))
      = (fun _ : Fin 2 => (1 / 2 : ℝ))
    ∧ IsDist ((fun i : Fin 2 => if i = 0 then (1 : ℝ) else 0)
        ᵥ* Matrix.of (fun _ _ : Fin 2 => (1 / 2 : ℝ))) := by
  have hS : IsDist (fun i : Fin 2 => if i = 0 then (1 : ℝ) else 0) := by
    refine ⟨?_, ?_⟩
    · intro i
      by_cases h : i = 0 <;> simp [h]
    · norm_num [Fin.sum_univ_two]
  have hrows : ∀ _ : Fin 2, IsDist (fun _ : Fin 2 => (1 / 2 : ℝ)) := by
    intro _
    refine ⟨fun _ => by norm_num, ?_⟩
    norm_num [Fin.sum_univ_two]
  refine ⟨?_, isDist_vecMul hS hrows⟩
  funext o
  simp [Matrix.vecMul_apply_eq_sum]

/-- T5: the classifier-level earthmover bound, applied to the constant
fair-coin classifier and the two point masses. -/
private theorem t5_classifier_earthmover :
    tvDist ((fun i : Fin 2 => if i = 0 then (1 : ℝ) else 0)
        ᵥ* Matrix.of (fun _ _ : Fin 2 => (1 / 2 : ℝ)))
      ((fun i : Fin 2 => if i = 0 then (0 : ℝ) else 1)
        ᵥ* Matrix.of (fun _ _ : Fin 2 => (1 / 2 : ℝ)))
    ≤ earthmover d2 delta0D delta1D := by
  exact tvDist_vecMul_le_earthmover t2_const_fair delta0D.2 delta1D.2

/-- The deterministic identity classifier on `Fin 2`: individual `x`
receives outcome `x` with probability `1`. -/
private def idClassifier : Fin 2 → Fin 2 → ℝ := fun x o => if o = x then 1 else 0

/-- T6: the identity classifier is individually fair for the discrete
metric, and for the two opposite point masses both sides of the
earthmover bound are independently computed to be `1` (the induced
distributions are the point masses themselves, the unique coupling
has cost `1`). Neither value is obtained from
`tvDist_vecMul_le_earthmover`. -/
private theorem t6_identity_values :
    IsLipschitzFair d2 idClassifier
    ∧ tvDist
        ((fun i : Fin 2 => if i = 0 then (1 : ℝ) else 0) ᵥ* Matrix.of idClassifier)
        ((fun i : Fin 2 => if i = 0 then (0 : ℝ) else 1) ᵥ* Matrix.of idClassifier) = 1
    ∧ earthmover d2 delta0D delta1D = 1 := by
  have hrows : ∀ x : Fin 2, IsDist (idClassifier x) := by
    intro x
    fin_cases x <;>
      refine ⟨fun o => by fin_cases o <;> norm_num [idClassifier], ?_⟩ <;>
      norm_num [idClassifier, Fin.sum_univ_two]
  have hind0 : (fun i : Fin 2 => if i = 0 then (1 : ℝ) else 0) ᵥ* Matrix.of idClassifier =
      (fun i : Fin 2 => if i = 0 then (1 : ℝ) else 0) := by
    funext o
    fin_cases o <;>
      norm_num [Matrix.vecMul_apply_eq_sum, idClassifier, Fin.sum_univ_two]
  have hind1 : (fun i : Fin 2 => if i = 0 then (0 : ℝ) else 1) ᵥ* Matrix.of idClassifier =
      (fun i : Fin 2 => if i = 0 then (0 : ℝ) else 1) := by
    funext o
    fin_cases o <;>
      norm_num [Matrix.vecMul_apply_eq_sum, idClassifier, Fin.sum_univ_two]
  refine ⟨⟨hrows, ?_⟩, ?_, ?_⟩
  · intro x y
    fin_cases x <;> fin_cases y <;>
      norm_num [idClassifier, d2, tvDist, Fin.sum_univ_two]
  · rw [hind0, hind1]
    norm_num [tvDist, Fin.sum_univ_two]
  · have hcost : ∀ π : {π // IsCoupling delta0D.1 delta1D.1 π},
        transportCost d2 π.1 = 1 := by
      intro π
      obtain ⟨hnn, hrow, hcol⟩ := π.2
      have r0 := hrow 0
      have r1 := hrow 1
      have c0 := hcol 0
      have c1 := hcol 1
      simp only [delta0D, delta1D, Fin.sum_univ_two] at r0 r1 c0 c1
      norm_num at r0 r1 c0 c1
      have n00 := hnn 0 0
      have n01 := hnn 0 1
      have n10 := hnn 1 0
      have n11 := hnn 1 1
      have h01 : π.1 0 1 = 1 := by linarith
      have h00 : π.1 0 0 = 0 := by linarith
      have h10 : π.1 1 0 = 0 := by linarith
      have h11 : π.1 1 1 = 0 := by linarith
      unfold transportCost
      norm_num [Fin.sum_univ_two, d2, h00, h01, h10, h11]
    unfold earthmover
    have : Nonempty {π // IsCoupling delta0D.1 delta1D.1 π} :=
      nonempty_couplingSubtype delta0D delta1D
    have hfun : (fun π : {π // IsCoupling delta0D.1 delta1D.1 π} =>
        transportCost d2 π.1) = fun _ => (1 : ℝ) :=
      funext hcost
    rw [hfun]
    exact ciInf_const

/-- The off-diagonal cost `1 / 2` on `Fin 2`: `0` on the diagonal and `1 / 2` off it. -/
private noncomputable def dHalf : Fin 2 → Fin 2 → ℝ := fun x y => if x = y then 0 else 1 / 2

/-- T7: the earthmover bound needs fairness for the cost on its right side. The identity
classifier is individually fair for `d2` (T6), but for the opposite point masses its outcome
distributions are `1` apart in total variation distance while their earthmover value for
`dHalf` is `1 / 2`, so the bound fails for `dHalf` and the identity classifier is not
individually fair with respect to `dHalf`. -/
private theorem t7_bound_needs_same_cost :
    earthmover dHalf delta0D delta1D = 1 / 2
    ∧ ¬ tvDist
        ((fun i : Fin 2 => if i = 0 then (1 : ℝ) else 0) ᵥ* Matrix.of idClassifier)
        ((fun i : Fin 2 => if i = 0 then (0 : ℝ) else 1) ᵥ* Matrix.of idClassifier)
      ≤ earthmover dHalf delta0D delta1D
    ∧ ¬ IsLipschitzFair dHalf idClassifier := by
  have hem : earthmover dHalf delta0D delta1D = 1 / 2 := by
    have hcost : ∀ π : {π // IsCoupling delta0D.1 delta1D.1 π},
        transportCost dHalf π.1 = 1 / 2 := by
      intro π
      obtain ⟨hnn, hrow, hcol⟩ := π.2
      have r0 := hrow 0
      have r1 := hrow 1
      have c0 := hcol 0
      have c1 := hcol 1
      simp only [delta0D, delta1D, Fin.sum_univ_two] at r0 r1 c0 c1
      norm_num at r0 r1 c0 c1
      have n00 := hnn 0 0
      have n01 := hnn 0 1
      have n10 := hnn 1 0
      have n11 := hnn 1 1
      have h01 : π.1 0 1 = 1 := by linarith
      have h00 : π.1 0 0 = 0 := by linarith
      have h10 : π.1 1 0 = 0 := by linarith
      have h11 : π.1 1 1 = 0 := by linarith
      unfold transportCost
      norm_num [Fin.sum_univ_two, dHalf, h00, h01, h10, h11]
    unfold earthmover
    have : Nonempty {π // IsCoupling delta0D.1 delta1D.1 π} :=
      nonempty_couplingSubtype delta0D delta1D
    have hfun : (fun π : {π // IsCoupling delta0D.1 delta1D.1 π} =>
        transportCost dHalf π.1) = fun _ => (1 / 2 : ℝ) :=
      funext hcost
    rw [hfun]
    exact ciInf_const
  have htv := t6_identity_values.2.1
  have hgap : ¬ tvDist
      ((fun i : Fin 2 => if i = 0 then (1 : ℝ) else 0) ᵥ* Matrix.of idClassifier)
      ((fun i : Fin 2 => if i = 0 then (0 : ℝ) else 1) ᵥ* Matrix.of idClassifier)
      ≤ earthmover dHalf delta0D delta1D := by
    rw [htv, hem]
    norm_num
  refine ⟨hem, hgap, fun h => ?_⟩
  have h01 := h.2 0 1
  norm_num [tvDist, idClassifier, dHalf, Fin.sum_univ_two] at h01

end Cslib.MachineLearning.IndividualFairness
