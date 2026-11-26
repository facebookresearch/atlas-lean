/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import PhyslibExt.Mechanics.MachineElements
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Tests for `PhyslibExt.Mechanics.MachineElements`

* a train with two external meshes and one internal mesh: its ratio `1/24`, its external-mesh
  count, a no-slip motion, lossless mesh port torques, the shaft loads and the cancelling port
  powers;
* the same train with the output orientation swapped but the sign unchanged, which is rejected;
* four-bar linkages: a non-Grashof linkage in a closed regular configuration with determinant
  `-2` and velocity ratios `(1 / 2, 1)`, and its local branch with that velocity map; a
  parallelogram linkage at a dead center, where the determinant vanishes; and a ground link
  longer than the other three links together, which admits no closed configuration.
-/

@[expose] public section

namespace PhyslibExtTest.Mechanics.MachineElements

open _root_.Mechanics.MachineElements

/-! ## A. Two external meshes and one internal mesh -/

/-- Two external meshes and one internal mesh: `20 → 40` external, `15 → 45` external,
`18 → 72` internal (pinion upstream, ring downstream). -/
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

/-! ## D. Four-bar linkages -/

/-- A four-bar with ground `1`, crank `1`, coupler `2` and rocker `√2`; it is not a Grashof
linkage (`1 + 2 > 1 + √2`). -/
noncomputable def exampleLinkage : FourBar :=
  ⟨1, 1, 2, Real.sqrt 2, one_pos, one_pos, two_pos, Real.sqrt_pos.mpr two_pos⟩

/-- A noncollinear closed configuration with nonzero transmission: crank vertical
(`θ₂ = π / 2`), coupler horizontal (`θ₃ = 0`), rocker at `θ₄ = π / 4`; the dependent-angle
determinant is `-2`, and the velocity ratios are `ω₃ / ω₂ = 1 / 2`, `ω₄ / ω₂ = 1`. -/
lemma exampleLinkage_regular :
    exampleLinkage.IsClosed (Real.pi / 2) 0 (Real.pi / 4) ∧
      (exampleLinkage.dependentJacobian 0 (Real.pi / 4)).det = -2 ∧
      exampleLinkage.velocityRatio (Real.pi / 2) 0 (Real.pi / 4) = (1 / 2, 1) := by
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hs2 : Real.sqrt 2 ≠ 0 := by positivity
  have e1 : (0 : ℝ) - Real.pi / 4 = -(Real.pi / 4) := by ring
  have e2 : Real.pi / 4 - Real.pi / 2 = -(Real.pi / 4) := by ring
  have e3 : (0 : ℝ) - Real.pi / 2 = -(Real.pi / 2) := by ring
  refine ⟨?_, ?_, ?_⟩
  · simp only [FourBar.IsClosed, FourBar.closure, exampleLinkage, Real.cos_pi_div_two,
      Real.sin_pi_div_two, Real.cos_zero, Real.sin_zero, Real.cos_pi_div_four,
      Real.sin_pi_div_four]
    ext
    · simp only [Prod.fst_zero]
      nlinarith [h2]
    · simp only [Prod.snd_zero]
      nlinarith [h2]
  · rw [FourBar.det_dependentJacobian]
    simp only [exampleLinkage, e1, Real.sin_neg, Real.sin_pi_div_four]
    nlinarith [h2]
  · simp only [FourBar.velocityRatio, exampleLinkage, e1, e2, e3, Real.sin_neg,
      Real.sin_pi_div_four, Real.sin_pi_div_two]
    ext
    · field_simp
    · field_simp
      nlinarith [h2]

/-- A parallelogram four-bar: ground `2`, crank `1`, coupler `2`, rocker `1`. -/
def parallelogramLinkage : FourBar :=
  ⟨2, 1, 2, 1, two_pos, one_pos, two_pos, one_pos⟩

/-- A dead center: with all links along the ground line (`θ₂ = θ₃ = θ₄ = 0`) the parallelogram
four-bar is closed and its dependent-angle determinant vanishes. -/
lemma parallelogramLinkage_deadCenter :
    parallelogramLinkage.IsClosed 0 0 0 ∧ (parallelogramLinkage.dependentJacobian 0 0).det = 0 := by
  refine ⟨?_, ?_⟩
  · simp only [FourBar.IsClosed, FourBar.closure, parallelogramLinkage, Real.cos_zero,
      Real.sin_zero]
    ext <;> norm_num
  · rw [FourBar.det_dependentJacobian]
    simp

/-- A four-bar whose ground `10` exceeds crank, coupler and rocker `1` together. -/
def longGroundLinkage : FourBar :=
  ⟨10, 1, 1, 1, by norm_num, one_pos, one_pos, one_pos⟩

/-- Incompatible lengths have no closed configuration. -/
lemma longGroundLinkage_not_isClosed (θ₂ θ₃ θ₄ : ℝ) :
    ¬ longGroundLinkage.IsClosed θ₂ θ₃ θ₄ := by
  exact longGroundLinkage.not_isClosed_of_lt_ground (by simp [longGroundLinkage]; norm_num) θ₂ θ₃ θ₄

-- The regular configuration has a local branch through it whose velocity map is `(1 / 2, 1)`.
example : ∃ ψ : ℝ → ℝ × ℝ, ψ (Real.pi / 2) = (0, Real.pi / 4) ∧
    HasDerivAt ψ (1 / 2, 1) (Real.pi / 2) := by
  obtain ⟨h, hdet, hv⟩ := exampleLinkage_regular
  obtain ⟨ψ, h0, -, -, hD⟩ := exampleLinkage.exists_local_branch h (by rw [hdet]; norm_num)
  exact ⟨ψ, h0, hv ▸ hD⟩

-- The dead center satisfies the general criterion: coupler and rocker are collinear,
-- `θ₃ - θ₄ = 0 * π`.
example : (parallelogramLinkage.dependentJacobian 0 0).det = 0 :=
  (parallelogramLinkage.det_dependentJacobian_eq_zero_iff 0 0).2 ⟨0, by simp⟩

end PhyslibExtTest.Mechanics.MachineElements

end
