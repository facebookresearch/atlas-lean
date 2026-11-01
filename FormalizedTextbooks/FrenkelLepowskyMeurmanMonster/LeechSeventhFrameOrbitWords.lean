/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechSeventhFrameOrbitData

/-! The finite signed-word certificates bind to the genuine spatial and quotient actions. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix BigOperators
set_option backward.isDefEq.respectTransparency false

/-- An original section generator or its genuine group inverse. -/
def leechSeventhFrameLetter (l : Fin 18 × Bool) : leechIsomSubgroup :=
  if l.2 then (generatedFifthSectionGenerator l.1)⁻¹ else generatedFifthSectionGenerator l.1

/-- The actual spatial group element of an original signed word. -/
def leechSeventhFrameWord (w : List (Fin 18 × Bool)) : leechIsomSubgroup :=
  (w.map leechSeventhFrameLetter).prod

/-- Every original signed letter preserves the genuine selected E8 section. -/
theorem leechSeventhFrameLetter_mem (l : Fin 18 × Bool) :
    leechSeventhFrameLetter l ∈ leechSeventhE8SectionGroup := by
  rcases l with ⟨g, b⟩
  cases b
  · exact generatedAxisE8FrameSystemOrbitGenerator_mem g
  · exact leechSeventhE8SectionGroup.inv_mem (generatedAxisE8FrameSystemOrbitGenerator_mem g)

/-- Every original signed word lies in the actual full section group. -/
theorem leechSeventhFrameWord_mem (w : List (Fin 18 × Bool)) :
    leechSeventhFrameWord w ∈ leechSeventhE8SectionGroup := by
  apply Subgroup.list_prod_mem
  intro g hg
  obtain ⟨l, _, rfl⟩ := List.mem_map.mp hg
  exact leechSeventhFrameLetter_mem l

/-- The actual short-line image of a signed letter has the checked original root address. -/
theorem leechSeventhFrameLetter_root_label (l : Fin 18 × Bool) (r : Fin 120) :
    griessShortPermutation (leechSeventhFrameLetter l) (leechSeventhE8RootLabel r) =
      leechSeventhE8RootLabel (leechSeventhFrameLetterRoot l r) := by
  rcases l with ⟨g, b⟩
  cases b
  · exact leechSeventhE8Root_label_action g r
  · change griessShortPermutation (generatedFifthSectionGenerator g)⁻¹
      (leechSeventhE8RootLabel r) = leechSeventhE8RootLabel (leechSeventhFrameRootInverse g r)
    apply (griessShortPermutation (generatedFifthSectionGenerator g)).injective
    rw [map_inv]
    change (griessShortPermutation (generatedFifthSectionGenerator g))
      ((griessShortPermutation (generatedFifthSectionGenerator g)).symm
        (leechSeventhE8RootLabel r)) = _
    rw [Equiv.apply_symm_apply, leechSeventhE8Root_label_action,
      leechSeventhFrameRootInverse_certificate]

/-- The checked root-address word agrees with the original full group action on short lines. -/
theorem leechSeventhFrameWord_root_label (w : List (Fin 18 × Bool)) (r : Fin 120) :
    griessShortPermutation (leechSeventhFrameWord w) (leechSeventhE8RootLabel r) =
      leechSeventhE8RootLabel (leechSeventhFrameWordRoot w r) := by
  induction w with
  | nil =>
    simp only [leechSeventhFrameWord, List.map_nil, List.prod_nil, map_one]
    rfl
  | cons l w ih =>
    have hw : leechSeventhFrameWord (l :: w) =
        leechSeventhFrameLetter l * leechSeventhFrameWord w := rfl
    rw [hw, map_mul]
    change griessShortPermutation (leechSeventhFrameLetter l)
      (griessShortPermutation (leechSeventhFrameWord w) (leechSeventhE8RootLabel r)) = _
    rw [ih, leechSeventhFrameLetter_root_label]
    rfl

/-- The signed inverse matrix certificate binds to the actual lattice quotient action. -/
theorem leechSeventhFrameLetter_binary (l : Fin 18 × Bool) (a : Fin 8 → ZMod 2) :
    leechModTwoAction (leechSeventhFrameLetter l) (generatedAxisE8FrameRootEmbedding a) =
      generatedAxisE8FrameRootEmbedding (leechSeventhFrameLetterMatrix l *ᵥ a) := by
  rcases l with ⟨g, b⟩
  cases b
  · exact generatedFifthSectionGenerator_binary g a
  · have h := generatedFifthSectionGenerator_binary g
      (leechSeventhFrameInverseMatrix g *ᵥ a)
    rw [Matrix.mulVec_mulVec, leechSeventhFrameInverseMatrix_certificate, Matrix.one_mulVec] at h
    change leechModTwoAction (generatedFifthSectionGenerator g)⁻¹
      (generatedAxisE8FrameRootEmbedding a) = _
    apply (leechModTwoAction (generatedFifthSectionGenerator g)).injective
    rw [map_inv]
    change (leechModTwoAction (generatedFifthSectionGenerator g))
      ((leechModTwoAction (generatedFifthSectionGenerator g)).symm
        (generatedAxisE8FrameRootEmbedding a)) = _
    rw [LinearEquiv.apply_symm_apply]
    exact h.symm

/-- The adjacent-state word replay is the original whole lattice quotient action. -/
theorem leechSeventhFrameWord_binary (w : List (Fin 18 × Bool)) (a : Fin 8 → ZMod 2) :
    leechModTwoAction (leechSeventhFrameWord w) (generatedAxisE8FrameRootEmbedding a) =
      generatedAxisE8FrameRootEmbedding (leechSeventhFrameWordBinary w a) := by
  induction w with
  | nil =>
    simp only [leechSeventhFrameWord, List.map_nil, List.prod_nil, map_one]
    rfl
  | cons l w ih =>
    have hw : leechSeventhFrameWord (l :: w) =
        leechSeventhFrameLetter l * leechSeventhFrameWord w := rfl
    rw [hw, map_mul]
    change leechModTwoAction (leechSeventhFrameLetter l)
      (leechModTwoAction (leechSeventhFrameWord w) (generatedAxisE8FrameRootEmbedding a)) = _
    rw [ih, leechSeventhFrameLetter_binary]
    rfl

/-- The actual full-section root index of a signed word is its checked finite root address. -/
theorem leechSeventhFrameWord_section_root_index (w : List (Fin 18 × Bool)) (r : Fin 120) :
    leechSeventhE8SectionRootIndex ⟨leechSeventhFrameWord w, leechSeventhFrameWord_mem w⟩ r =
      leechSeventhFrameWordRoot w r := by
  apply leechSeventhE8RootLabel_injective
  rw [leechSeventhE8SectionRootIndex_label, leechSeventhFrameWord_root_label]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
