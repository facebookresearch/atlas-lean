/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisE8FrameSystemsMaskRecognition

/-! The displayed singular four-spaces cannot be enlarged to singular subspaces.
A finite check tests only the four displayed basis vectors against each outside vector. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- A compact obstruction to adjoining a vector to a candidate singular space. -/
def generatedAxisE8FrameCandidateMaximalCheck (k : Fin 270) : Bool :=
  (List.finRange 256).all (fun x =>
    if (generatedAxisE8FrameCandidateMask k).testBit x.val then true else
    if generatedAxisE8FrameSingularMask.testBit x.val then
      !(List.finRange 4).all (fun j => generatedAxisE8FrameSingularMask.testBit
        (generatedAxisE8FrameLabelXor x (generatedAxisE8FrameSystemBasisLabels k j)).val)
    else true)

set_option maxHeartbeats 1000000000 in
-- There are270 candidates,256 possible adjoined labels and four basis tests.
set_option maxRecDepth 10000 in
-- Nested finite arrays require deeper ordinary kernel reduction.
/-- Every candidate has a kernel-checked obstruction to singular enlargement. -/
theorem generatedAxisE8FrameCandidate_maximal_certificate (k : Fin 270) :
    generatedAxisE8FrameCandidateMaximalCheck k = true := by
  revert k
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
