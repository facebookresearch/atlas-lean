/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthSectionPackedForwardCheck00
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthSectionPackedForwardCheck01
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthSectionPackedForwardCheck02
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthSectionPackedForwardCheck03
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthSectionPackedForwardCheck04
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthSectionPackedForwardCheck05
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthSectionPackedForwardCheck06
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthSectionPackedInverseCertificates

/-! Every signed original section word has its checked complete actual binary replay. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

/-- Every positive packed matrix is the complete actual original binary source action. -/
theorem generatedTwelfth_section_packed_forward_actual (g : Fin 18) :
    generatedTwelfthSectionBinaryMatrix g =
      sixthFrameOrbitColumnMatrix (generatedTwelfthSectionPackedForward g) := by
  by_cases h : g.val < 12
  · exact generatedTwelfth_section_packed_forward_0 ⟨g.val, h⟩
  · obtain ⟨k, rfl⟩ : ∃ k : Fin 6, g = Fin.natAdd 12 k := by
      refine ⟨⟨g.val - 12, by omega⟩, Fin.ext ?_⟩
      dsimp [Fin.natAdd]
      omega
    fin_cases k
    · exact generatedTwelfth_section_packed_forward_1
    · exact generatedTwelfth_section_packed_forward_2
    · exact generatedTwelfth_section_packed_forward_3
    · exact generatedTwelfth_section_packed_forward_4
    · exact generatedTwelfth_section_packed_forward_5
    · exact generatedTwelfth_section_packed_forward_6

/-- All inverse packets are genuine right inverses of the actual full source actions. -/
theorem generatedTwelfth_section_packed_backward_actual (g : Fin 18) :
    generatedTwelfthSectionBinaryMatrix g *
      sixthFrameOrbitColumnMatrix (generatedTwelfthSectionPackedBackward g) = 1 := by
  rw [generatedTwelfth_section_packed_forward_actual]
  exact generatedTwelfth_section_packed_inverse g

/-- Arbitrary complete signed source words replay their genuine lattice binary action. -/
theorem generatedTwelfth_section_word_binary_actual
    (w : List (Fin 18 × Bool)) (v : Fin 24 → ZMod 2) :
    leechBinaryAction ((w.map generatedTwelfthRootOrbitLetter).prod).val v =
      w.foldr (generatedTwelfthSectionSignedBinary
        (fun g => sixthFrameOrbitColumnMatrix (generatedTwelfthSectionPackedBackward g))) v :=
  generatedTwelfth_section_word_binary_generic _
    generatedTwelfth_section_packed_backward_actual w v

/-- Each of the three original whole matrix fixers has its complete genuine binary source replay. -/
theorem generatedTwelfth_matrix_fixer_binary_actual (g : Fin 3) (v : Fin 24 → ZMod 2) :
    leechBinaryAction (generatedTwelfthMatrixFixer g).val v =
      (generatedTwelfthMatrixFixerWord g).foldr (generatedTwelfthSectionSignedBinary
        (fun k => sixthFrameOrbitColumnMatrix (generatedTwelfthSectionPackedBackward k))) v :=
  generatedTwelfth_matrix_fixer_binary_generic _
    generatedTwelfth_section_packed_backward_actual g v

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
