/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthRootKernel
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthGoldenOrbitAxisMatrices

/-! The full actual section root-line permutation action retains its genuine matrix kernel. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The actual root-line addresses respect the full original group multiplication. -/
theorem generatedTwelfth_root_index_mul (g h : leechSeventhE8SectionGroup) (r : Fin 120) :
    leechSeventhE8SectionRootIndex (g * h) r =
      leechSeventhE8SectionRootIndex g (leechSeventhE8SectionRootIndex h r) := by
  apply leechSeventhE8RootLabel_injective
  rw [leechSeventhE8SectionRootIndex_label]
  change griessShortPermutation (g.val * h.val) (leechSeventhE8RootLabel r) = _
  rw [map_mul]
  change griessShortPermutation g.val
    (griessShortPermutation h.val (leechSeventhE8RootLabel r)) = _
  rw [← leechSeventhE8SectionRootIndex_label h,
    ← leechSeventhE8SectionRootIndex_label g]

/-- The identity actual section isometry fixes every original root-line address. -/
theorem generatedTwelfth_root_index_one (r : Fin 120) :
    leechSeventhE8SectionRootIndex 1 r = r := by
  apply leechSeventhE8RootLabel_injective
  rw [leechSeventhE8SectionRootIndex_label]
  change griessShortPermutation 1 (leechSeventhE8RootLabel r) = _
  rw [map_one]
  rfl

/-- Every full section isometry induces a genuine permutation of the original 120 root lines. -/
def generatedTwelfthRootPermutation (g : leechSeventhE8SectionGroup) : Equiv.Perm (Fin 120) where
  toFun := leechSeventhE8SectionRootIndex g
  invFun := leechSeventhE8SectionRootIndex g⁻¹
  left_inv r := by
    rw [← generatedTwelfth_root_index_mul, inv_mul_cancel, generatedTwelfth_root_index_one]
  right_inv r := by
    rw [← generatedTwelfth_root_index_mul, mul_inv_cancel, generatedTwelfth_root_index_one]

/-- The original section group has its genuine finite root-line permutation homomorphism. -/
def generatedTwelfthRootAction : leechSeventhE8SectionGroup →* Equiv.Perm (Fin 120) where
  toFun := generatedTwelfthRootPermutation
  map_one' := by
    apply Equiv.ext
    intro r
    exact generatedTwelfth_root_index_one r
  map_mul' g h := by
    apply Equiv.ext
    intro r
    exact generatedTwelfth_root_index_mul g h r

/-- Every actual root-action kernel element fixes every full inserted physical section matrix. -/
theorem generatedTwelfth_root_action_kernel_matrix (g : generatedTwelfthRootAction.ker)
    (M : Matrix (Fin 8) (Fin 8) ℝ) :
    conwayMatrixAction g.val.val (generatedTwelfthSectionMatrix M) =
      generatedTwelfthSectionMatrix M := by
  apply generatedTwelfth_root_kernel_matrix_fixed
  intro r
  exact congrArg (fun p : Equiv.Perm (Fin 120) => p r) g.property

/-- The genuine root-line kernel fixes the whole actual Twelfth axis matrix. -/
theorem generatedTwelfth_root_action_kernel_actual_matrix (g : generatedTwelfthRootAction.ker) :
    conwayMatrixAction g.val.val (griessConwayEncode generatedTwelfthAxis).1 =
      (griessConwayEncode generatedTwelfthAxis).1 := by
  rw [← generatedTwelfthGoldenOrbit_axis_base]
  unfold generatedTwelfthGoldenOrbitAxisMatrix
  rw [map_smul, map_add, map_nsmul, conwayMatrixAction_one,
    generatedTwelfth_root_action_kernel_matrix]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
