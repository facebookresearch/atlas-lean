/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.Mechanics.EngineeringStatics
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Tests for `PhyslibExt.Mechanics.EngineeringStatics`

* a balanced couple: zero resultant and the moment `e₃` about every reference point;
* a single force: its moment changes with the reference point, the transport law predicts the
  change, and the units law rescales the moment;
* a force normal to the plane of the first two axes: its moment lies in that plane, and the
  planar projection loses it.
-/

@[expose] public section

open scoped Matrix

namespace PhyslibExtTest.Mechanics.EngineeringStatics

open _root_.Mechanics.EngineeringStatics _root_.PhyslibExt.Mechanics.HarmonicMechanics

/-! ## A. A balanced couple -/

/-- A balanced couple: the force `e₂` at `e₁` and the force `-e₂` at the origin. -/
def couplePoint : Fin 2 → Fin 3 → ℝ :=
  ![![1, 0, 0], ![0, 0, 0]]

/-- The two opposite forces of the balanced couple. -/
def coupleForce : Fin 2 → Fin 3 → ℝ :=
  ![![0, 1, 0], ![0, -1, 0]]

/-- The balanced couple has zero resultant and the nonzero moment `e₃` about every reference
point. -/
lemma couple_fixture :
    resultantForce coupleForce = 0 ∧
      ∀ O : Fin 3 → ℝ, momentAbout couplePoint coupleForce (fun _ => 0) O = ![0, 0, 1] := by
  refine ⟨?_, ?_⟩
  · unfold resultantForce coupleForce
    rw [Fin.sum_univ_two]
    ext i
    fin_cases i <;> simp
  · intro O
    unfold momentAbout couplePoint coupleForce
    rw [Fin.sum_univ_two]
    ext j
    fin_cases j <;> simp [cross_apply]

-- Origin invariance from the zero resultant alone: the couple has the same moment about any two
-- reference points.
example (O O' : Fin 3 → ℝ) :
    momentAbout couplePoint coupleForce (fun _ => 0) O' =
      momentAbout couplePoint coupleForce (fun _ => 0) O :=
  momentAbout_eq_of_resultantForce_eq_zero couple_fixture.1 O O'

/-! ## B. A single force -/

/-- One force `e₂` applied at `e₁`, without couple. -/
def leverPoint : Fin 1 → Fin 3 → ℝ :=
  ![![1, 0, 0]]

/-- The single force of the lever fixture. -/
def leverForce : Fin 1 → Fin 3 → ℝ :=
  ![![0, 1, 0]]

/-- A nonzero resultant changes the origin moment: the force `e₂` at `e₁` has moment `e₃` about
the origin and moment `0` about its point of application. -/
lemma lever_fixture :
    resultantForce leverForce = ![0, 1, 0] ∧
      momentAbout leverPoint leverForce (fun _ => 0) 0 = ![0, 0, 1] ∧
      momentAbout leverPoint leverForce (fun _ => 0) ![1, 0, 0] = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · unfold resultantForce leverForce
    rw [Fin.sum_univ_one, Matrix.cons_val_zero]
  · unfold momentAbout leverPoint leverForce
    rw [Fin.sum_univ_one]
    ext i
    fin_cases i <;> simp [cross_apply]
  · unfold momentAbout leverPoint leverForce
    rw [Fin.sum_univ_one]
    simp

-- The transport law predicts the moment about the point of application from the moment about
-- the origin: `e₃ + (0 - e₁) ⨯₃ e₂ = 0`.
example : momentAbout leverPoint leverForce (fun _ => 0) ![1, 0, 0] = 0 := by
  rw [momentAbout_eq_add_cross leverPoint leverForce (fun _ => 0) 0 ![1, 0, 0],
    lever_fixture.2.1, lever_fixture.1]
  ext i
  fin_cases i <;> simp [cross_apply]

-- A nonzero resultant: some reference point changes the moment about the origin.
example : ∃ O' : Fin 3 → ℝ,
    momentAbout leverPoint leverForce (fun _ => 0) O' ≠
      momentAbout leverPoint leverForce (fun _ => 0) 0 := by
  refine exists_momentAbout_ne_of_resultantForce_ne_zero ?_ 0
  rw [lever_fixture.1]
  intro h
  have h1 := congrFun h 1
  simp at h1

-- Units: in millimetres and kilonewtons (length factor `1000`, force factor `1 / 1000`) the
-- moment factor is `1000 * (1 / 1000) = 1`, so the moment about the origin is still `e₃`.
example :
    (wrenchAbout (fun i => (1000 : ℝ) • leverPoint i) (fun i => (1 / 1000 : ℝ) • leverForce i)
        (fun _ => ((1000 : ℝ) * (1 / 1000)) • (0 : Fin 3 → ℝ)) ((1000 : ℝ) • 0)).moment =
      ![0, 0, 1] := by
  rw [wrenchAbout_smul, lever_fixture.2.1]
  ext i
  fin_cases i <;> norm_num

-- The planar moment of the projected force is the third component `1` of its moment `e₃`.
example :
    moment2D (fun i => planarPart (leverPoint i)) (fun i => planarPart (leverForce i)) = 1 := by
  rw [moment2D_planarPart, lever_fixture.2.1]
  simp

/-! ## C. A force normal to the plane -/

/-- One force `e₃`, normal to the plane of the first two axes, applied at `e₂`. -/
def normalPoint : Fin 1 → Fin 3 → ℝ :=
  ![![0, 1, 0]]

/-- The single force of the planar-loss fixture. -/
def normalForce : Fin 1 → Fin 3 → ℝ :=
  ![![0, 0, 1]]

/-- A planar projection can lose an out-of-plane moment: the force `e₃` at `e₂` has moment `e₁`
about the origin, while its projection has zero planar resultant and zero planar moment. -/
lemma normal_fixture :
    momentAbout normalPoint normalForce (fun _ => 0) 0 = ![1, 0, 0] ∧
      resultantForce (fun i => planarPart (normalForce i)) = 0 ∧
      moment2D (fun i => planarPart (normalPoint i)) (fun i => planarPart (normalForce i)) = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · unfold momentAbout normalPoint normalForce
    rw [Fin.sum_univ_one]
    ext i
    fin_cases i <;> simp [cross_apply]
  · unfold resultantForce planarPart normalForce
    rw [Fin.sum_univ_one]
    ext i
    fin_cases i <;> simp
  · unfold moment2D planarPart normalPoint normalForce
    rw [Fin.sum_univ_one]
    simp

end PhyslibExtTest.Mechanics.EngineeringStatics

end
