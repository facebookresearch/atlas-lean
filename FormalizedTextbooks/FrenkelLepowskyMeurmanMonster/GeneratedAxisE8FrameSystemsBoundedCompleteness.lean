/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisE8FrameSystemsFirstLabel
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisE8FrameSystemsCandidateSpan
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisE8FrameSystemsAdmissible
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisE8FrameSystemsTagBinding

/-! Pigeonhole bounds the first greedy label below32, so two checked label blocks
suffice for completeness of the270 genuine candidate subspaces. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- A checked greedy-label cover exhausts all genuine intrinsic sixteen-element singular spaces. -/
theorem generatedAxisE8FrameSystems_complete_of_bounded_coverage
    (hcover : ∀ a : Fin 32, generatedAxisE8FrameCandidateCoverageAt
      ⟨a.val, by omega⟩)
    (W : Submodule (ZMod 2) (Fin 8 → ZMod 2))
    (hW : W ∈ generatedAxisE8IntrinsicFrameSystems) :
    ∃ k : Fin 270, generatedAxisE8FrameSystemCandidate k = W := by
  obtain ⟨l, hl, hg, hs⟩ := generatedAxisE8Frame_greedy_basis W hW.1
  obtain ⟨v0, v1, v2, v3, rfl⟩ := List.length_eq_four.mp hl
  let a := generatedAxisE8FrameLabel v0
  let b := generatedAxisE8FrameLabel v1
  let c := generatedAxisE8FrameLabel v2
  let d := generatedAxisE8FrameLabel v3
  have ha : generatedAxisE8FrameAdmissibleLabels [a] := by
    have he := generatedAxisE8Frame_admissible_of_greedy W
      ([v0, v1, v2, v3].take 1) (generatedAxisE8FrameGreedyIn_take W _ hg 1) hW.2
    simpa [a] using he
  have hb : generatedAxisE8FrameAdmissibleLabels [a, b] := by
    have he := generatedAxisE8Frame_admissible_of_greedy W
      ([v0, v1, v2, v3].take 2) (generatedAxisE8FrameGreedyIn_take W _ hg 2) hW.2
    simpa [a, b] using he
  have hc : generatedAxisE8FrameAdmissibleLabels [a, b, c] := by
    have he := generatedAxisE8Frame_admissible_of_greedy W
      ([v0, v1, v2, v3].take 3) (generatedAxisE8FrameGreedyIn_take W _ hg 3) hW.2
    simpa [a, b, c] using he
  have hd : generatedAxisE8FrameAdmissibleLabels [a, b, c, d] := by
    have he := generatedAxisE8Frame_admissible_of_greedy W [v0, v1, v2, v3] hg hW.2
    simpa [a, b, c, d] using he
  let k := generatedAxisE8FrameCandidateIndex a b c d
  have hal : a.val < 32 :=
    generatedAxisE8FrameGreedy_first_label W hW.1 v0 v1 v2 v3 hg
  have htag := hcover ⟨a.val, hal⟩ ha b hb c hc d hd
  have hlabels := generatedAxisE8FrameCandidateIndex_binding a b c d htag
  have h0 : generatedAxisE8FrameSystemBasisLabels k 0 = a := by
    simpa only [Matrix.cons_val_zero] using congrFun hlabels 0
  have h1 : generatedAxisE8FrameSystemBasisLabels k 1 = b := by
    simpa using congrFun hlabels 1
  have h2 : generatedAxisE8FrameSystemBasisLabels k 2 = c := by
    simpa using congrFun hlabels 2
  have h3 : generatedAxisE8FrameSystemBasisLabels k 3 = d := by
    simpa using congrFun hlabels 3
  have hb0 : generatedAxisE8FrameSystemCandidateBasis k 0 = v0 := by
    change generatedAxisE8FrameLabelBits (generatedAxisE8FrameSystemBasisLabels k 0) = v0
    rw [h0]; exact generatedAxisE8FrameLabel_right v0
  have hb1 : generatedAxisE8FrameSystemCandidateBasis k 1 = v1 := by
    change generatedAxisE8FrameLabelBits (generatedAxisE8FrameSystemBasisLabels k 1) = v1
    rw [h1]; exact generatedAxisE8FrameLabel_right v1
  have hb2 : generatedAxisE8FrameSystemCandidateBasis k 2 = v2 := by
    change generatedAxisE8FrameLabelBits (generatedAxisE8FrameSystemBasisLabels k 2) = v2
    rw [h2]; exact generatedAxisE8FrameLabel_right v2
  have hb3 : generatedAxisE8FrameSystemCandidateBasis k 3 = v3 := by
    change generatedAxisE8FrameLabelBits (generatedAxisE8FrameSystemBasisLabels k 3) = v3
    rw [h3]; exact generatedAxisE8FrameLabel_right v3
  refine ⟨k, ?_⟩
  rw [generatedAxisE8FrameSystemCandidate_span, hb0, hb1, hb2, hb3]
  exact hs

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
