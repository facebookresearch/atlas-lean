/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisE8FrameSystemsCandidateData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisE8FrameSystemsCoverageData

/-! Exact binding of finite candidate tags to the genuine four-column intrinsic basis data. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 200000000 in
-- The270 cached candidate tags are checked against their four literal basis labels.
set_option maxRecDepth 10000 in
-- The270-row basis literal has a deeply nested tuple representation.
/-- Every cached tag is the exact four-byte tag of its displayed intrinsic basis. -/
theorem generatedAxisE8FrameCandidateTags_binding : ∀ k : Fin 270,
    generatedAxisE8FrameCandidateTags[k.val]! = generatedAxisE8FrameBasisTag
      (generatedAxisE8FrameSystemBasisLabels k 0) (generatedAxisE8FrameSystemBasisLabels k 1)
      (generatedAxisE8FrameSystemBasisLabels k 2) (generatedAxisE8FrameSystemBasisLabels k 3) := by
  decide +kernel

/-- A four-byte tag retains all four finite basis labels without collisions. -/
theorem generatedAxisE8FrameBasisTag_injective (a b c d A B C D : Fin 256)
    (he : generatedAxisE8FrameBasisTag a b c d = generatedAxisE8FrameBasisTag A B C D) :
    a = A ∧ b = B ∧ c = C ∧ d = D := by
  unfold generatedAxisE8FrameBasisTag at he
  have ha := a.isLt; have hb := b.isLt; have hc := c.isLt; have hd := d.isLt
  have hA := A.isLt; have hB := B.isLt; have hC := C.isLt; have hD := D.isLt
  have hae : a.val = A.val := by omega
  have hbe : b.val = B.val := by omega
  have hce : c.val = C.val := by omega
  have hde : d.val = D.val := by omega
  exact ⟨Fin.ext hae, Fin.ext hbe, Fin.ext hce, Fin.ext hde⟩

/-- A successful compact tag lookup gives the exact displayed four-label basis. -/
theorem generatedAxisE8FrameCandidateIndex_binding (a b c d : Fin 256)
    (he : generatedAxisE8FrameCandidateTags[(generatedAxisE8FrameCandidateIndex a b c d).val]! =
      generatedAxisE8FrameBasisTag a b c d) :
    (fun i : Fin 4 => generatedAxisE8FrameSystemBasisLabels
      (generatedAxisE8FrameCandidateIndex a b c d) i) = ![a, b, c, d] := by
  rw [generatedAxisE8FrameCandidateTags_binding] at he
  obtain ⟨ha, hb, hc, hd⟩ := generatedAxisE8FrameBasisTag_injective _ _ _ _ _ _ _ _ he
  ext i
  fin_cases i <;> simp [ha, hb, hc, hd]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
