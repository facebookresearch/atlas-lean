/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.Circuits.LosslessDCFlowModel
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
Two-node fixture with a forward line (node `0` to node `1`, `b = 2`) and a
reversed line (node `1` to node `0`, `b = 3`) at angles `(1/2, 0)`.
-/

@[expose] public section

namespace PhyslibExtTest.Circuits.LosslessDCFlowModel

open PhyslibExt.Circuits.ACInjectionLossBalance
open PhyslibExt.Circuits.ArcPortSigns
open PhyslibExt.Circuits.LosslessDCFlowModel

/-- Branch tails: branch `0` leaves node `0`, branch `1` leaves node `1`. -/
def tl : Fin 2 → Fin 2 := ![0, 1]

/-- Branch heads: branch `0` enters node `1`, and branch `1` is the
reversed line, entering node `0`. -/
def hd : Fin 2 → Fin 2 := ![1, 0]

/-- Positive branch susceptances. -/
def bb : Fin 2 → ℝ := ![2, 3]

/-- Node phase angles, with node `1` as the phase reference. -/
noncomputable def th : Fin 2 → ℝ := ![1 / 2, 0]

lemma bb_pos : ∀ e, 0 < bb e := by
  intro e
  fin_cases e <;> norm_num [bb]

/-- Incidence entries: `+1` at each tail, `-1` at each head. -/
example :
    electricalIncidence tl hd 0 0 = 1 ∧ electricalIncidence tl hd 1 0 = -1 ∧
      electricalIncidence tl hd 0 1 = -1 ∧ electricalIncidence tl hd 1 1 = 1 := by
  simp [electricalIncidence_apply, tl, hd]

/-- Forward flow `2 * (1/2 - 0) = 1`; reversed-line flow `3 * (0 - 1/2) = -3/2`. -/
example :
    dcBranchFlow 2 2 tl hd bb th 0 = 1 ∧ dcBranchFlow 2 2 tl hd bb th 1 = -3 / 2 := by
  simp only [dcBranchFlow_apply]
  norm_num [tl, hd, bb, th]

/-- Reversing both orientations negates the forward flow. -/
example : dcBranchFlow 2 2 hd tl bb th 0 = -1 := by
  rw [dcBranchFlow_reverse, dcBranchFlow_apply]
  norm_num [tl, hd, bb, th]

/-- Injections `p = (5/2, -5/2)`, balanced over the two nodes. -/
example :
    dcInjection 2 2 tl hd bb th 0 = 5 / 2 ∧ dcInjection 2 2 tl hd bb th 1 = -5 / 2 ∧
      ∑ v : Fin 2, dcInjection 2 2 tl hd bb th v = 0 := by
  refine ⟨?_, ?_, sum_dcInjection_eq_zero 2 2 tl hd bb th⟩ <;>
    simp [dcInjection, Matrix.mulVec, dotProduct, Fin.sum_univ_two, dcBranchFlow_apply,
      electricalIncidence_apply, tl, hd, bb, th] <;> norm_num

/-- The weighted Laplacian is `[[5, -5], [-5, 5]]`. -/
example :
    weightedLaplacian 2 2 tl hd bb 0 0 = 5 ∧ weightedLaplacian 2 2 tl hd bb 0 1 = -5 ∧
      weightedLaplacian 2 2 tl hd bb 1 0 = -5 ∧ weightedLaplacian 2 2 tl hd bb 1 1 = 5 := by
  simp [weightedLaplacian, Matrix.mul_apply, Fin.sum_univ_two, electricalIncidence_apply,
    tl, hd, bb]
  norm_num

/-- `L_b * θ` reproduces the injections `(5/2, -5/2)`. -/
example : Matrix.mulVec (weightedLaplacian 2 2 tl hd bb) th = ![5 / 2, -5 / 2] := by
  rw [← dcInjection_eq_weightedLaplacian_mulVec]
  funext v
  fin_cases v <;>
    simp [dcInjection, Matrix.mulVec, dotProduct, Fin.sum_univ_two, dcBranchFlow_apply,
      electricalIncidence_apply, tl, hd, bb, th] <;> norm_num

/-- Energy `θ ⬝ᵥ L_b θ = 2 * (1/2)^2 + 3 * (-1/2)^2 = 5/4`. -/
example : dotProduct th (Matrix.mulVec (weightedLaplacian 2 2 tl hd bb) th) = 5 / 4 := by
  rw [dotProduct_weightedLaplacian_mulVec]
  norm_num [Fin.sum_univ_two, tl, hd, bb, th]

/-- Every node is reachable from the reference node `1` through a
positive-susceptance branch. -/
lemma reachable_from_one :
    ∀ v, (MathlibExt.Combinatorics.Graph.ArcNetworkLaplacian.positiveArcGraph tl hd bb).Reachable
      1 v := by
  have hadj : (MathlibExt.Combinatorics.Graph.ArcNetworkLaplacian.positiveArcGraph
      tl hd bb).Adj 1 0 :=
    (SimpleGraph.fromRel_adj _ _ _).mpr
      ⟨by decide, Or.inr ⟨0, by norm_num [bb], by simp [tl], by simp [hd]⟩⟩
  intro v
  fin_cases v
  · exact hadj.reachable
  · exact SimpleGraph.Reachable.refl _

/-- The kernel of `L_b` is the constant angle vectors, so the angles
`(1/2, 0)` are not in it. -/
example : Matrix.mulVec (weightedLaplacian 2 2 tl hd bb) th ≠ 0 := by
  rw [ne_eq, weightedLaplacian_mulVec_eq_zero_iff_of_reachable 2 2 tl hd bb
    (fun e => (bb_pos e).le) 1 reachable_from_one]
  intro h
  have h0 := h 0
  norm_num [th] at h0

/-- Grounding node `1` leaves an invertible block. -/
example : IsUnit ((weightedLaplacian 2 2 tl hd bb).submatrix
    (Subtype.val : {v : Fin 2 // v ≠ 1} → Fin 2)
    (Subtype.val : {v : Fin 2 // v ≠ 1} → Fin 2)) :=
  grounded_weightedLaplacian_isUnit 2 2 tl hd bb (fun e => (bb_pos e).le) 1 reachable_from_one

/-- The phase reference has unit voltage `1`. -/
example : unitVoltage 2 th 1 = 1 :=
  unitVoltage_eq_one_of_angle_eq_zero 2 th 1 (by simp [th])

/-- AC real power: `2 sin(1/2)` on the forward line, `3 sin(-1/2)` on the
reversed line. -/
example :
    acBranchRealPower 2 2 tl hd bb th 0 = 2 * Real.sin (1 / 2) ∧
      acBranchRealPower 2 2 tl hd bb th 1 = 3 * Real.sin (-(1 / 2)) := by
  simp only [acBranchRealPower_eq_mul_sin]
  norm_num [tl, hd, bb, th]

/-- Cubic bound on the forward line, `|2 sin(1/2) - 1| ≤ 1/24`, with a
strictly positive gap. -/
example :
    |2 * Real.sin (1 / 2) - 1| ≤ 1 / 24 ∧ 0 < |2 * Real.sin (1 / 2) - 1| := by
  have h := abs_acBranchRealPower_sub_dcBranchFlow_le 2 2 tl hd bb bb_pos th 0
  rw [acBranchRealPower_eq_mul_sin, dcBranchFlow_apply] at h
  norm_num [tl, hd, bb, th] at h
  refine ⟨by linarith [h], abs_pos.mpr ?_⟩
  have hlt := Real.sin_lt (show (0 : ℝ) < 1 / 2 by norm_num)
  linarith

/-- Cubic bound on the reversed line, `|3 sin(-1/2) + 3/2| ≤ 1/16`. -/
example : |3 * Real.sin (-(1 / 2)) + 3 / 2| ≤ 1 / 16 := by
  have h := abs_acBranchRealPower_sub_dcBranchFlow_le 2 2 tl hd bb bb_pos th 1
  rw [acBranchRealPower_eq_mul_sin, dcBranchFlow_apply] at h
  norm_num [tl, hd, bb, th] at h ⊢
  linarith [h]

/-- The headline instantiated on the fixture. -/
example : ∀ e, |acBranchRealPower 2 2 tl hd bb th e - dcBranchFlow 2 2 tl hd bb th e| ≤
    bb e * |th (tl e) - th (hd e)| ^ 3 / 6 :=
  (model_correct 2 2 tl hd bb bb_pos th).2.2.2

/-- The lossless network absorbs zero total real power. -/
example :
    ∑ v : Fin 2, (nodeComplexPower 2 2 (electricalIncidence tl hd) (unitVoltage 2 th)
      (losslessAdmittance 2 bb) (fun _ => 0) v).re = 0 :=
  sum_nodeRealPower_eq_zero 2 2 tl hd bb th

end PhyslibExtTest.Circuits.LosslessDCFlowModel
