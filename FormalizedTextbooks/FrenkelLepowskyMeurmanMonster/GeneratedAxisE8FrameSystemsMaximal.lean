/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisE8FrameSystemsMaximalData

/-! The checked adjoining-vector obstruction proves actual maximality of every candidate. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster


/-- Any totally singular subspace containing a candidate equals that candidate. -/
theorem generatedAxisE8FrameSystemCandidate_maximal (k : Fin 270)
    (W : Submodule (ZMod 2) (Fin 8 → ZMod 2))
    (hKW : generatedAxisE8FrameSystemCandidate k ≤ W)
    (hq : ∀ v ∈ W, generatedAxisE8FrameQuadratic v = 0) :
    W = generatedAxisE8FrameSystemCandidate k := by
  apply le_antisymm ?_ hKW
  intro v hv
  let x := generatedAxisE8FrameLabel v
  have hbits : generatedAxisE8FrameLabelBits x = v := generatedAxisE8FrameLabel_right v
  by_contra hn
  have hm : (generatedAxisE8FrameCandidateMask k).testBit x.val = false := by
    apply Bool.eq_false_iff.mpr
    intro he
    exact hn (hbits ▸ (generatedAxisE8FrameCandidateMask_mem_iff k x).mp he)
  have hs : generatedAxisE8FrameSingularMask.testBit x.val = true :=
    (generatedAxisE8FrameSingularMask_certificate x).mpr (hbits ▸ hq v hv)
  have hc := List.all_eq_true.mp (generatedAxisE8FrameCandidate_maximal_certificate k)
    x (List.mem_finRange x)
  change (if (generatedAxisE8FrameCandidateMask k).testBit x.val then true else
    if generatedAxisE8FrameSingularMask.testBit x.val then
      !(List.finRange 4).all (fun j => generatedAxisE8FrameSingularMask.testBit
        (generatedAxisE8FrameLabelXor x (generatedAxisE8FrameSystemBasisLabels k j)).val)
    else true) = true at hc
  rw [hm, hs] at hc
  have ha : (List.finRange 4).all (fun j => generatedAxisE8FrameSingularMask.testBit
      (generatedAxisE8FrameLabelXor x (generatedAxisE8FrameSystemBasisLabels k j)).val) = true := by
    apply List.all_eq_true.mpr
    intro j _
    apply (generatedAxisE8FrameSingularMask_certificate _).mpr
    rw [generatedAxisE8FrameLabelBits_xor, hbits]
    have hb : generatedAxisE8FrameSystemCandidateBasis k j ∈
        generatedAxisE8FrameSystemCandidate k := by
      refine ⟨Pi.single j 1, ?_⟩
      change Matrix.mulVec (fun i t => generatedAxisE8FrameSystemCandidateBasis k t i)
        (Pi.single j 1) = generatedAxisE8FrameSystemCandidateBasis k j
      exact Matrix.mulVec_single_one _ j
    exact hq _ (W.add_mem hv (hKW hb))
  simp [ha] at hc

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
