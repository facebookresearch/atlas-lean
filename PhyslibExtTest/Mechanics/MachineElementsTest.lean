/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.Mechanics.MachineElements
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Tests for `PhyslibExt.Mechanics.MachineElements`

* a train with two external meshes and one internal mesh: its ratio `1/24`, its external-mesh
  count, a no-slip motion, lossless mesh port torques, the shaft loads and the cancelling port
  powers;
* the same train with the output orientation swapped but the sign unchanged, which is rejected.
-/

@[expose] public section

namespace PhyslibExtTest.Mechanics.MachineElements

open _root_.Mechanics.MachineElements

/-! ## A. Two external meshes and one internal mesh -/

/-- Two external meshes and one internal mesh: `20 → 40` external, `15 → 45` external,
`18 → 72` internal (pinion driving a ring gear). -/
def exampleTrain : Fin 3 → Mesh :=
  ![⟨20, 40, .external, by decide⟩, ⟨15, 45, .external, by decide⟩,
    ⟨18, 72, .internal, by decide⟩]

/-- Mesh port torques of the example train loaded with `5` at the input. -/
def exampleUp : Fin 3 → ℝ := ![5, -10, 30]

/-- Downstream mesh port torques of the example train. -/
def exampleDown : Fin 3 → ℝ := ![10, -30, -120]

/-- The example train: ratio `(-1/2) * (-1/3) * (1/4) = 1/24`, two external meshes, and the
no-slip speeds `240, -120, 40, 10`. -/
lemma exampleTrain_ratio :
    trainRatio exampleTrain = 1 / 24 ∧ externalCount exampleTrain = 2 ∧
      IsNoSlip exampleTrain ![240, -120, 40, 10] := by
  refine ⟨?_, ?_, ?_⟩
  · unfold trainRatio
    rw [Fin.prod_univ_three]
    simp [exampleTrain, Mesh.ratio, MeshKind.sense]
    norm_num
  · unfold externalCount exampleTrain
    decide
  · intro k
    fin_cases k
    · simp [exampleTrain, Mesh.ratio, MeshKind.sense]
      norm_num
    · simp [exampleTrain, Mesh.ratio, MeshKind.sense]
      norm_num
    · simp [exampleTrain, Mesh.ratio, MeshKind.sense]
      norm_num

/-- The example port torques are lossless; the shaft loads are `5, 0, 0, -120`, and the port
powers `5 * 240` and `-120 * 10` cancel. -/
lemma exampleTrain_torques :
    IsLossless exampleTrain exampleUp exampleDown ∧
      shaftLoad exampleUp exampleDown 0 = 5 ∧ shaftLoad exampleUp exampleDown 1 = 0 ∧
      shaftLoad exampleUp exampleDown 2 = 0 ∧ shaftLoad exampleUp exampleDown 3 = -120 ∧
      ∑ j, shaftLoad exampleUp exampleDown j * (![240, -120, 40, 10] : Fin 4 → ℝ) j = 0 := by
  have hLossless : IsLossless exampleTrain exampleUp exampleDown := by
    intro k
    fin_cases k
    · intro w
      simp [exampleTrain, exampleUp, exampleDown, Mesh.ratio, MeshKind.sense]
      ring
    · intro w
      simp [exampleTrain, exampleUp, exampleDown, Mesh.ratio, MeshKind.sense]
      ring
    · intro w
      simp [exampleTrain, exampleUp, exampleDown, Mesh.ratio, MeshKind.sense]
      ring
  have h0 : shaftLoad exampleUp exampleDown 0 = 5 := by simp [shaftLoad, exampleUp]
  have h1 : shaftLoad exampleUp exampleDown 1 = 0 := by
    simp [shaftLoad, exampleUp, exampleDown, Fin.sum_univ_three]
  have h2 : shaftLoad exampleUp exampleDown 2 = 0 := by
    simp [shaftLoad, exampleUp, exampleDown, Fin.sum_univ_three]
  have h3 : shaftLoad exampleUp exampleDown 3 = -120 := by
    simp [shaftLoad, exampleUp, exampleDown, Fin.sum_univ_three]
  have hSum :
      ∑ j, shaftLoad exampleUp exampleDown j * (![240, -120, 40, 10] : Fin 4 → ℝ) j = 0 := by
    rw [Fin.sum_univ_four]
    rw [h0, h1, h2, h3]
    norm_num
  exact ⟨hLossless, h0, h1, h2, h3, hSum⟩

/-- Swapped output orientation with the unchanged sign: the reoriented output speed `-10` is
not the train ratio times the input speed `240`. -/
lemma exampleTrain_orientation_rejected :
    (-10 : ℝ) ≠ trainRatio exampleTrain * 240 := by
  have hR := exampleTrain_ratio.1
  rw [hR]
  norm_num

/-! ## B. Positive tooth counts -/

-- Tooth counts are positive by construction, so no positivity hypothesis is needed: the
-- example train has a nonzero ratio, and its single-mesh restriction to the first external
-- mesh turns the output against the input.
example : trainRatio exampleTrain ≠ 0 := trainRatio_ne_zero

example : ¬ 0 < trainRatio (fun _ : Fin 1 => exampleTrain 0) := by
  rw [trainRatio_pos_iff]
  decide

/-! ## C. Realizable internal meshes -/

-- An internal mesh needs a ring with more teeth than its pinion: no mesh has equal tooth counts
-- `20` and `20` on an internal pair.
example : ¬ ∃ g : Mesh, g.driverTeeth = 20 ∧ g.drivenTeeth = 20 ∧ g.kind = .internal := by
  rintro ⟨g, h1, h2, h3⟩
  have h := g.driverTeeth_lt_drivenTeeth_of_internal h3
  rw [h1, h2] at h
  exact lt_irrefl _ h

-- The same counts on an external mesh are a valid mesh, with ratio `-1`.
example : (⟨20, 20, .external, by decide⟩ : Mesh).ratio = -1 := by
  simp [Mesh.ratio, MeshKind.sense]

end PhyslibExtTest.Mechanics.MachineElements

end
