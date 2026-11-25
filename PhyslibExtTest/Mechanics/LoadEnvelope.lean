/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.Mechanics.LoadEnvelope
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Load-box envelope checks

Concrete consumers of `PhyslibExt.Mechanics.LoadEnvelope`:
a mixed-sign four-coordinate influence vector with upper
envelope `13` and lower envelope `-6`, endpoint
attainment on both sides, zero-capacity and empty-index
boundaries, feasibility and box-violation controls, and
the supported bridge at the focused truss fixture with
influence vector `![1, -1]`.

## i. Overview

These are elaboration, sign, and non-vacuity checks, not
new results.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Generic box envelope
- B. Supported bridge

## iv. References

- `PhyslibExt.Mechanics.LoadEnvelope`
- `PhyslibExt.Mechanics.TrussCompatibility`
-/

open Matrix
open Mechanics.TrussCompatibility
open Mechanics.LoadEnvelope

namespace PhyslibExtTest.Mechanics.LoadEnvelope

/-! ## A. Generic box envelope -/

/-- Mixed-sign influence vector `(2, -3, 0, 5)`. -/
private abbrev eta4 : Fin 4 → ℝ := ![2, -3, 0, 5]

/-- Capacities `(4, 2, 7, 1)`: upper envelope
`2 * 4 + 5 * 1 = 13`, lower envelope `-3 * 2 = -6`; the
zero coefficient keeps its capacity `7` in both endpoint
loads. -/
private noncomputable abbrev cap4 : Fin 4 → ℝ := ![4, 2, 7, 1]

private lemma cap4_nonneg : ∀ i, 0 ≤ cap4 i := by
  intro i
  fin_cases i <;> norm_num [cap4]

/-- Upper attainment at the mixed-sign data: endpoint
load `(4, 0, 7, 1)`, response `13`. -/
example : upperBoxLoad eta4 cap4 = ![4, 0, 7, 1]
    ∧ eta4 ⬝ᵥ upperBoxLoad eta4 cap4 = 13 := by
  have h := upperBoxLoad_attains_boxUpper eta4 cap4 cap4_nonneg
  refine ⟨by funext i; fin_cases i <;>
    norm_num [upperBoxLoad, eta4, cap4], ?_⟩
  rw [h.2.2]
  norm_num [Fin.sum_univ_four, eta4, cap4]

/-- Lower attainment at the mixed-sign data: endpoint
load `(0, 2, 7, 0)`, response `-6`. -/
example : lowerBoxLoad eta4 cap4 = ![0, 2, 7, 0]
    ∧ eta4 ⬝ᵥ lowerBoxLoad eta4 cap4 = -6 := by
  have h := lowerBoxLoad_attains_boxLower eta4 cap4 cap4_nonneg
  refine ⟨by funext i; fin_cases i <;>
    norm_num [lowerBoxLoad, eta4, cap4], ?_⟩
  rw [h.2.2]
  norm_num [Fin.sum_univ_four, eta4, cap4]

/-- The zero coefficient keeps its capacity in both
endpoint loads. -/
example : upperBoxLoad eta4 cap4 2 = 7
    ∧ lowerBoxLoad eta4 cap4 2 = 7 := by
  norm_num [upperBoxLoad, lowerBoxLoad, eta4, cap4]

/-- A pattern load inside the box: response `4`, between
the envelope values. -/
example : eta4 ⬝ᵥ ![1, 1, 1, 1] = 4
    ∧ eta4 ⬝ᵥ ![1, 1, 1, 1] ≤ 13
    ∧ -6 ≤ eta4 ⬝ᵥ ![1, 1, 1, 1] := by
  have hup := dotProduct_le_boxUpper eta4 cap4 ![1, 1, 1, 1]
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num [cap4])
  have hlo := boxLower_le_dotProduct eta4 cap4 ![1, 1, 1, 1]
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num [cap4])
  have hsumU : (∑ i, cap4 i * max (eta4 i) 0) = 13 := by
    norm_num [Fin.sum_univ_four, eta4, cap4]
  have hsumL : (∑ i, cap4 i * min (eta4 i) 0) = -6 := by
    norm_num [Fin.sum_univ_four, eta4, cap4]
  rw [hsumU] at hup
  rw [hsumL] at hlo
  exact ⟨by norm_num [dotProduct, Fin.sum_univ_four, eta4],
    hup, hlo⟩

/-- Zero capacities: both endpoint loads are zero and the
envelope values are zero. -/
example : upperBoxLoad eta4 0 = 0 ∧ lowerBoxLoad eta4 0 = 0
    ∧ (∑ i, (0 : Fin 4 → ℝ) i * max (eta4 i) 0) = 0 := by
  refine ⟨by funext i; simp [upperBoxLoad], by
    funext i; simp [lowerBoxLoad], by simp⟩

/-- Empty index: every pairing and envelope sum is the
empty sum. -/
example (eta cap f : Fin 0 → ℝ) : eta ⬝ᵥ f = 0
    ∧ (∑ i, cap i * max (eta i) 0) = 0 := by
  simp [dotProduct]

/-- Negative capacity makes the upper endpoint load
infeasible, which is what the attainment premise buys;
the box itself is empty. -/
example : ¬ 0 ≤ upperBoxLoad (![1] : Fin 1 → ℝ) (![-1] : Fin 1 → ℝ) 0
    ∧ ∀ f : Fin 1 → ℝ, ¬ (0 ≤ f 0 ∧ f 0 ≤ -1) := by
  refine ⟨by norm_num [upperBoxLoad], ?_⟩
  intro f hf
  linarith [hf.1, hf.2]

/-- Over-capacity violation: response `2` escapes the
upper envelope `1`. -/
example :
    ¬ (![1] : Fin 1 → ℝ) ⬝ᵥ ![2]
      ≤ ∑ i, (![1] : Fin 1 → ℝ) i * max ((![1] : Fin 1 → ℝ) i) 0 := by
  norm_num [dotProduct, Fin.sum_univ_one]

/-- Below-zero violation: response `-1` escapes below
the lower envelope `0`. -/
example :
    ¬ ∑ i, (![1] : Fin 1 → ℝ) i * min ((![1] : Fin 1 → ℝ) i) 0
      ≤ (![1] : Fin 1 → ℝ) ⬝ᵥ ![-1] := by
  norm_num [dotProduct, Fin.sum_univ_one]

/-! ## B. Supported bridge -/

/-- Joints for the focused two-coordinate check. -/
private abbrev rF : Fin 3 → (Fin 2 → ℝ) := ![![0, 0], ![2, 0], ![1, 1]]

/-- Selection of joint 1's two coordinates. -/
private abbrev SF : Matrix (Fin 3 × Fin 2) (Fin 2) ℝ :=
  Matrix.of fun q f =>
    if (q = (1, 0) ∧ f = 0) ∨ (q = (1, 1) ∧ f = 1) then 1 else 0

/-- Supported action on the focused fixture:
`B S *ᵥ v = (2 v₀, v₀ - v₁)`. -/
private lemma supportedActionF (v : Fin 2 → ℝ) (e : Fin 2) :
    ((axialCompatibility rF ![0, 1] ![1, 2] * SF) *ᵥ v) e
      = ![2 * v 0, v 0 - v 1] e := by
  rw [← Matrix.mulVec_mulVec, axialCompatibility_mulVec_apply]
  fin_cases e
  · simp [Fin.sum_univ_two, SF, Matrix.mulVec, dotProduct]
  · simp [Fin.sum_univ_two, SF, Matrix.mulVec, dotProduct]
    ring

private lemma kernelF : ∀ v : Fin 2 → ℝ,
    (axialCompatibility rF ![0, 1] ![1, 2] * SF) *ᵥ v = 0 → v = 0 := by
  intro v hv
  have h0 := congrFun hv 0
  have h1 := congrFun hv 1
  rw [supportedActionF] at h0 h1
  simp at h0 h1
  funext i
  fin_cases i <;> simp <;> linarith

/-- The focused stiffness is `[[5, -3], [-3, 3]]`. -/
private lemma supportedStiffnessF :
    (axialCompatibility rF ![0, 1] ![1, 2] * SF)ᵀ
        * Matrix.diagonal ![1 / 2, 3]
        * (axialCompatibility rF ![0, 1] ![1, 2] * SF)
      = !![5, -3; -3, 3] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.transpose_apply, Matrix.diagonal,
      axialCompatibility, SF, Matrix.of_apply, Fin.sum_univ_two, -Matrix.transpose_of] <;> norm_num

private lemma posDefBox :
    ((axialCompatibility rF ![0, 1] ![1, 2] * SF)ᵀ
      * Matrix.diagonal ![1 / 2, 3]
      * (axialCompatibility rF ![0, 1] ![1, 2] * SF)).PosDef :=
  (supported_posDef_iff rF ![0, 1] ![1, 2] SF _
    (by intro e; fin_cases e <;> norm_num)).mpr kernelF

/-- Mixed-sign influence vector at output `![8, -6]`. -/
private lemma etaMixed :
    influenceVector rF ![0, 1] ![1, 2] SF ![1 / 2, 3] ![8, -6]
      = ![1, -1] := by
  have h : ((axialCompatibility rF ![0, 1] ![1, 2] * SF)ᵀ
        * Matrix.diagonal ![1 / 2, 3]
        * (axialCompatibility rF ![0, 1] ![1, 2] * SF)) *ᵥ ![1, -1]
      = ![8, -6] := by
    rw [supportedStiffnessF]
    funext i
    fin_cases i <;>
      norm_num [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  have h2 := (supported_mulVec_eq_iff_inv_mulVec rF ![0, 1] ![1, 2] SF _
    posDefBox).mp h
  exact h2.symm

/-- Supported upper attainment at the mixed-sign
influence vector: endpoint load `(4, 0)`, response `4`. -/
example :
    unitLoadResponse rF ![0, 1] ![1, 2] SF ![1 / 2, 3] ![8, -6]
        (upperBoxLoad
          (influenceVector rF ![0, 1] ![1, 2] SF ![1 / 2, 3]
            ![8, -6]) ![4, 2])
      = 4 := by
  have h := supported_boxUpper_attained rF ![0, 1] ![1, 2] SF
    ![1 / 2, 3] ![8, -6] ![4, 2]
    (by intro i; fin_cases i <;> norm_num)
  rw [h.2.2, etaMixed]
  norm_num [Fin.sum_univ_two]

/-- Supported lower attainment at the mixed-sign
influence vector: endpoint load `(0, 2)`, response `-2`. -/
example :
    unitLoadResponse rF ![0, 1] ![1, 2] SF ![1 / 2, 3] ![8, -6]
        (lowerBoxLoad
          (influenceVector rF ![0, 1] ![1, 2] SF ![1 / 2, 3]
            ![8, -6]) ![4, 2])
      = -2 := by
  have h := supported_boxLower_attained rF ![0, 1] ![1, 2] SF
    ![1 / 2, 3] ![8, -6] ![4, 2]
    (by intro i; fin_cases i <;> norm_num)
  rw [h.2.2, etaMixed]
  norm_num [Fin.sum_univ_two]

/-- A supported pattern load inside the box: response
`0`, between the supported envelope values `-2` and
`4`. -/
example :
    unitLoadResponse rF ![0, 1] ![1, 2] SF ![1 / 2, 3] ![8, -6]
        ![1, 1]
      = 0
    ∧ unitLoadResponse rF ![0, 1] ![1, 2] SF ![1 / 2, 3]
          ![8, -6] ![1, 1]
      ≤ 4
    ∧ -2
      ≤ unitLoadResponse rF ![0, 1] ![1, 2] SF ![1 / 2, 3]
          ![8, -6] ![1, 1] := by
  have hup := supported_unitLoadResponse_le_boxUpper rF
    ![0, 1] ![1, 2] SF ![1 / 2, 3] ![8, -6] ![4, 2] ![1, 1]
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
  have hlo := supported_boxLower_le_unitLoadResponse rF
    ![0, 1] ![1, 2] SF ![1 / 2, 3] ![8, -6] ![4, 2] ![1, 1]
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
  have hsumU :
      (∑ i, ![4, 2] i
        * max (influenceVector rF ![0, 1] ![1, 2] SF
          ![1 / 2, 3] ![8, -6] i) 0) = 4 := by
    rw [etaMixed]
    norm_num [Fin.sum_univ_two]
  have hsumL :
      (∑ i, ![4, 2] i
        * min (influenceVector rF ![0, 1] ![1, 2] SF
          ![1 / 2, 3] ![8, -6] i) 0) = -2 := by
    rw [etaMixed]
    norm_num [Fin.sum_univ_two]
  rw [hsumU] at hup
  rw [hsumL] at hlo
  have h0 :
      unitLoadResponse rF ![0, 1] ![1, 2] SF ![1 / 2, 3]
          ![8, -6] ![1, 1]
        = 0 := by
    rw [unitLoadResponse_apply, etaMixed]
    norm_num [dotProduct, Fin.sum_univ_two]
  exact ⟨h0, hup, hlo⟩

#print axioms Mechanics.LoadEnvelope.dotProduct_le_boxUpper
#print axioms Mechanics.LoadEnvelope.upperBoxLoad_attains_boxUpper
#print axioms Mechanics.LoadEnvelope.boxLower_le_dotProduct
#print axioms Mechanics.LoadEnvelope.lowerBoxLoad_attains_boxLower
#print axioms
  Mechanics.LoadEnvelope.supported_unitLoadResponse_le_boxUpper
#print axioms Mechanics.LoadEnvelope.supported_boxUpper_attained
#print axioms
  Mechanics.LoadEnvelope.supported_boxLower_le_unitLoadResponse
#print axioms Mechanics.LoadEnvelope.supported_boxLower_attained

end PhyslibExtTest.Mechanics.LoadEnvelope
