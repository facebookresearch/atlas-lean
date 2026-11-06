/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthSectionBinaryActions
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthMatrixFixerRootWord

/-! Whole genuine section words retain all twenty-four lattice binary coordinates. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

/-- A right inverse cache suffices because the source binary action is genuinely injective. -/
theorem generatedTwelfth_section_inverse_binary_generic
    (g : Fin 18) (b : Matrix (Fin 24) (Fin 24) (ZMod 2))
    (hb : generatedTwelfthSectionBinaryMatrix g * b = 1) (v : Fin 24 → ZMod 2) :
    leechBinaryAction (generatedFifthSectionGenerator g)⁻¹ v = b *ᵥ v := by
  apply (leechBinaryAction (generatedFifthSectionGenerator g)).injective
  rw [map_inv]
  change (leechBinaryAction (generatedFifthSectionGenerator g))
    ((leechBinaryAction (generatedFifthSectionGenerator g)).symm v) = _
  rw [LinearEquiv.apply_symm_apply]
  rw [generatedTwelfth_section_generator_binary, Matrix.mulVec_mulVec, hb,
    Matrix.one_mulVec]

/-- Signed literal letters use their actual positive matrix or a certified inverse. -/
def generatedTwelfthSectionSignedBinary
    (back : Fin 18 → Matrix (Fin 24) (Fin 24) (ZMod 2))
    (l : Fin 18 × Bool) (v : Fin 24 → ZMod 2) : Fin 24 → ZMod 2 :=
  (if l.2 then back l.1 else generatedTwelfthSectionBinaryMatrix l.1) *ᵥ v

/-- Each entire positive or inverse source letter has its complete genuine binary action. -/
theorem generatedTwelfth_section_letter_binary_generic
    (back : Fin 18 → Matrix (Fin 24) (Fin 24) (ZMod 2))
    (hback : ∀ g, generatedTwelfthSectionBinaryMatrix g * back g = 1)
    (l : Fin 18 × Bool) (v : Fin 24 → ZMod 2) :
    leechBinaryAction (generatedTwelfthRootOrbitLetter l).val v =
      generatedTwelfthSectionSignedBinary back l v := by
  rcases l with ⟨g, b⟩
  cases b
  · exact generatedTwelfth_section_generator_binary g v
  · exact generatedTwelfth_section_inverse_binary_generic g (back g) (hback g) v

/-- Arbitrary full original section words preserve the proved complete binary replay. -/
theorem generatedTwelfth_section_word_binary_generic
    (back : Fin 18 → Matrix (Fin 24) (Fin 24) (ZMod 2))
    (hback : ∀ g, generatedTwelfthSectionBinaryMatrix g * back g = 1)
    (w : List (Fin 18 × Bool)) (v : Fin 24 → ZMod 2) :
    leechBinaryAction ((w.map generatedTwelfthRootOrbitLetter).prod).val v =
      w.foldr (generatedTwelfthSectionSignedBinary back) v := by
  induction w generalizing v with
  | nil => rw [List.map_nil, List.prod_nil]; change leechBinaryAction 1 v = v
           rw [map_one]; rfl
  | cons l w ih =>
    rw [List.map_cons, List.prod_cons]
    change leechBinaryAction
      ((generatedTwelfthRootOrbitLetter l).val *
        ((w.map generatedTwelfthRootOrbitLetter).prod).val) v = _
    rw [map_mul]
    change leechBinaryAction (generatedTwelfthRootOrbitLetter l).val
      (leechBinaryAction ((w.map generatedTwelfthRootOrbitLetter).prod).val v) = _
    rw [ih, generatedTwelfth_section_letter_binary_generic back hback]
    rfl

/-- Each of the three actual entire matrix fixers retains every binary source coordinate. -/
theorem generatedTwelfth_matrix_fixer_binary_generic
    (back : Fin 18 → Matrix (Fin 24) (Fin 24) (ZMod 2))
    (hback : ∀ g, generatedTwelfthSectionBinaryMatrix g * back g = 1)
    (g : Fin 3) (v : Fin 24 → ZMod 2) :
    leechBinaryAction (generatedTwelfthMatrixFixer g).val v =
      (generatedTwelfthMatrixFixerWord g).foldr
        (generatedTwelfthSectionSignedBinary back) v :=
  generatedTwelfth_section_word_binary_generic back hback _ v

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
