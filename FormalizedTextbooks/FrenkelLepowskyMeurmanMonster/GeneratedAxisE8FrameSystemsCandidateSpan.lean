/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisE8FrameSystemsCandidates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisE8FrameSystemsGreedy

/-! The candidate range is exactly the genuine span of its four displayed basis vectors. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The four displayed candidate vectors have exactly the same span as the candidate map range. -/
theorem generatedAxisE8FrameSystemCandidate_span (k : Fin 270) :
    generatedAxisE8FrameSystemCandidate k = generatedAxisE8FrameListSpan
      [generatedAxisE8FrameSystemCandidateBasis k 0,
        generatedAxisE8FrameSystemCandidateBasis k 1,
        generatedAxisE8FrameSystemCandidateBasis k 2,
        generatedAxisE8FrameSystemCandidateBasis k 3] := by
  unfold generatedAxisE8FrameSystemCandidate generatedAxisE8FrameSystemCandidateMap
  rw [Matrix.range_mulVecLin]
  unfold generatedAxisE8FrameListSpan
  congr 1
  ext v
  change (∃ i : Fin 4, generatedAxisE8FrameSystemCandidateBasis k i = v) ↔ _
  simp only [Set.mem_ofPred_eq, List.mem_cons, List.not_mem_nil, or_false]
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i <;> simp
  · rintro (h | h | h | h)
    · exact ⟨0, h.symm⟩
    · exact ⟨1, h.symm⟩
    · exact ⟨2, h.symm⟩
    · exact ⟨3, h.symm⟩

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
