/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFifthFrameIntersectionPreservation
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthMatrixRecognition

/-! Every genuine full-axis stabilizer lift preserves the selected actual fifteen-frame system. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Fixing the full fifth axis forces its actual spatial lift to preserve the frame system. -/
theorem generatedFifthFrameSystem_local_preserved (f : localFiberSubgroup)
    (hh : rhoLocal (localFiberIntoH f) generatedFifthAxis = generatedFifthAxis) :
    generatedFifthFrameSystem.map (leechModTwoAction f.val.2).toLinearMap =
      generatedFifthFrameSystem := by
  apply generatedFifthFrameSystem_preserved f.val.2
  · apply (generatedFifth_matrix_stabilizer_iff f.val.2).mp
    have he := congrArg (fun x : GriessSpace => (griessConwayEncode x).1) hh
    rw [show (griessConwayEncode (rhoLocal (localFiberIntoH f) generatedFifthAxis)).1 =
      conwayMatrixAction f.val.2 (griessConwayEncode generatedFifthAxis).1 from
        congrArg Prod.fst (localGriessRepresentation_encode f generatedFifthAxis)] at he
    exact he
  · intro v hv
    have hi := generatedFifth_axis_binary_image_invariant (localFiberIntoH f) hh v hv
    exact hi

/-- Every actual H element fixing the fifth axis has a spatial lift preserving its frame system. -/
theorem generatedFifthFrameSystem_H_preserved (h : H)
    (hh : rhoLocal h generatedFifthAxis = generatedFifthAxis) :
    ∃ f : localFiberSubgroup, localFiberIntoH f = h ∧
      generatedFifthFrameSystem.map (leechModTwoAction f.val.2).toLinearMap =
        generatedFifthFrameSystem := by
  obtain ⟨f, hf⟩ := QuotientGroup.mk'_surjective localDiagonalSubgroup h
  change localFiberIntoH f = h at hf
  refine ⟨f, hf, generatedFifthFrameSystem_local_preserved f ?_⟩
  rwa [hf]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
