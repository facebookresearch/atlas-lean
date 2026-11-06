/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthSectionPackedActions

/-! Packed integer replay retains every coordinate of arbitrary genuine section words. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

/-- Exact packed columns of each original positive or inverse section letter. -/
def generatedTwelfthSectionPackedLetterColumns (l : Fin 18 × Bool) : Fin 24 → ℕ :=
  if l.2 then generatedTwelfthSectionPackedBackward l.1
  else generatedTwelfthSectionPackedForward l.1

/-- Complete signed source words replay using exact ordinary binary XOR. -/
def generatedTwelfthSectionPackedMaskWord (w : List (Fin 18 × Bool)) (v : ℕ) : ℕ :=
  w.foldr (fun l => sixthFrameOrbitMaskApply (generatedTwelfthSectionPackedLetterColumns l)) v

/-- Every packed positive or inverse source letter is its actual whole lattice binary action. -/
theorem generatedTwelfth_section_letter_packed_actual (l : Fin 18 × Bool) (v : ℕ) :
    leechBinaryAction (generatedTwelfthRootOrbitLetter l).val
        (monsterCo1GeometryBinaryMaskDecode (n := 24) v) =
      monsterCo1GeometryBinaryMaskDecode
        (sixthFrameOrbitMaskApply (generatedTwelfthSectionPackedLetterColumns l) v) := by
  rcases l with ⟨g, b⟩
  cases b
  · change leechBinaryAction (generatedFifthSectionGenerator g)
      (monsterCo1GeometryBinaryMaskDecode (n := 24) v) = _
    rw [generatedTwelfth_section_generator_binary,
      generatedTwelfth_section_packed_forward_actual]
    exact (sixthFrameOrbitMaskApply_decode _ _).symm
  · change leechBinaryAction (generatedFifthSectionGenerator g)⁻¹
      (monsterCo1GeometryBinaryMaskDecode (n := 24) v) = _
    rw [generatedTwelfth_section_inverse_binary_generic g _
      (generatedTwelfth_section_packed_backward_actual g)]
    exact (sixthFrameOrbitMaskApply_decode _ _).symm

/-- Every arbitrary signed source word has the complete checked packed lattice binary action. -/
theorem generatedTwelfth_section_word_packed_actual (w : List (Fin 18 × Bool)) (v : ℕ) :
    leechBinaryAction ((w.map generatedTwelfthRootOrbitLetter).prod).val
        (monsterCo1GeometryBinaryMaskDecode (n := 24) v) =
      monsterCo1GeometryBinaryMaskDecode (generatedTwelfthSectionPackedMaskWord w v) := by
  induction w with
  | nil => rw [List.map_nil, List.prod_nil]; change leechBinaryAction 1 _ = _
           rw [map_one]; rfl
  | cons l w ih =>
    rw [List.map_cons, List.prod_cons]
    change leechBinaryAction
      ((generatedTwelfthRootOrbitLetter l).val *
        ((w.map generatedTwelfthRootOrbitLetter).prod).val) _ = _
    rw [map_mul]
    change leechBinaryAction (generatedTwelfthRootOrbitLetter l).val
      (leechBinaryAction ((w.map generatedTwelfthRootOrbitLetter).prod).val
        (monsterCo1GeometryBinaryMaskDecode (n := 24) v)) = _
    rw [ih, generatedTwelfth_section_letter_packed_actual]
    rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
