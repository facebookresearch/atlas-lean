/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFifthMonomialSchreierData

/-! Each bounded Schreier certificate is an equality of the actual original permutation words. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- A finite inverse-array certificate determines the genuine inverse of an abstract permutation. -/
theorem generatedFifthPermutation_inverse_forward (p : golayAutomorphismSubgroup)
    (F B : Fin 24 → Fin 24) (hF : ∀ i, p.val i = F i) (hB : ∀ i, F (B i) = i)
    (i : Fin 24) : (p⁻¹).val i = B i := by
  apply p.val.injective
  change p.val (p.val.symm i) = p.val (B i)
  rw [Equiv.apply_symm_apply, hF, hB]

/-- Original permutation words evaluate through any already certified physical arrays. -/
theorem generatedFifthPermutation_word_forward {I : Type*}
    (P : I → golayAutomorphismSubgroup) (F : I → Fin 24 → Fin 24)
    (hP : ∀ k i, (P k).val i = F k i) (w : List I) (i : Fin 24) :
    ((w.map P).prod).val i = w.foldr (fun k x => F k x) i := by
  induction w generalizing i with
  | nil => rfl
  | cons k w ih =>
    change (P k).val (((w.map P).prod).val i) = _
    rw [ih, hP]
    rfl

/-- The original six permutation words and their inverses. -/
def generatedFifthSixLetter (l : Fin 6 × Bool) : golayAutomorphismSubgroup :=
  if l.2 then (generatedFifthMonomialSpatialPermutation l.1)⁻¹
  else generatedFifthMonomialSpatialPermutation l.1

/-- Physical evaluation of an original letter is its already bound finite coordinate array. -/
theorem generatedFifthSixLetter_forward (l : Fin 6 × Bool) (i : Fin 24) :
    (generatedFifthSixLetter l).val i =
      if l.2 then generatedFifthSixBackward l.1 i
      else generatedFifthMonomialSpatialForward l.1 i := by
  rcases l with ⟨k, b⟩
  cases b
  · exact generatedFifthMonomialSpatial_forward k i
  · exact generatedFifthPermutation_inverse_forward
      (generatedFifthMonomialSpatialPermutation k) _ _
      (generatedFifthMonomialSpatial_forward k) (generatedFifthSixBackward_certificate k) i

/-- Finite evaluation of every signed original six-generator word is its genuine permutation. -/
theorem generatedFifthSixWord_forward (w : List (Fin 6 × Bool)) (i : Fin 24) :
    ((w.map generatedFifthSixLetter).prod).val i = generatedFifthSixFiniteWord w i := by
  exact generatedFifthPermutation_word_forward generatedFifthSixLetter
    (fun l x => if l.2 then generatedFifthSixBackward l.1 x
      else generatedFifthMonomialSpatialForward l.1 x) generatedFifthSixLetter_forward w i

/-- Every original positive selected-generator word evaluates through the bound physical arrays. -/
theorem generatedFifthSelectedWord_forward (w : List (Fin 5)) (i : Fin 24) :
    ((w.map generatedFifthSelectedOctadPermutation).prod).val i =
      w.foldr (fun k x => generatedFifthSelectedOctadForward k x) i := by
  exact generatedFifthPermutation_word_forward generatedFifthSelectedOctadPermutation
    generatedFifthSelectedOctadForward generatedFifthSelectedOctad_forward w i

/-- The original selected-generator representative of a genuine monomial system image. -/
def generatedFifthSystemRep (i : Fin 15) : golayAutomorphismSubgroup :=
  ((generatedFifthMonomialSystemWord i).map generatedFifthSelectedOctadPermutation).prod

/-- Each displayed representative coordinate is the actual original word coordinate. -/
theorem generatedFifthSystemRep_forward (i : Fin 15) (j : Fin 24) :
    (generatedFifthSystemRep i).val j = generatedFifthSystemRepForward i j := by
  rw [generatedFifthSystemRep, generatedFifthSelectedWord_forward,
    generatedFifthSystemRepForward_certificate]

/-- Each displayed inverse coordinate is the genuine inverse of the actual representative. -/
theorem generatedFifthSystemRep_backward (i : Fin 15) (j : Fin 24) :
    ((generatedFifthSystemRep i)⁻¹).val j = generatedFifthSystemRepBackward i j := by
  exact generatedFifthPermutation_inverse_forward (generatedFifthSystemRep i) _ _
    (generatedFifthSystemRep_forward i) (generatedFifthSystemRepBackward_certificate i) j

/-- Each original Schreier transition is its genuine six-generator word. -/
theorem generatedFifthSixSchreier_word (k : Fin 5) (i : Fin 15) :
    (generatedFifthSystemRep (generatedFifthMonomialSystemTransition k i))⁻¹ *
        generatedFifthSelectedOctadPermutation k * generatedFifthSystemRep i =
      ((generatedFifthSixSchreierWord k i).map generatedFifthSixLetter).prod := by
  apply Subtype.ext
  apply Equiv.ext
  intro j
  change ((generatedFifthSystemRep (generatedFifthMonomialSystemTransition k i))⁻¹).val
      ((generatedFifthSelectedOctadPermutation k).val ((generatedFifthSystemRep i).val j)) =
    (((generatedFifthSixSchreierWord k i).map generatedFifthSixLetter).prod).val j
  rw [generatedFifthSystemRep_backward, generatedFifthSelectedOctad_forward,
    generatedFifthSystemRep_forward, generatedFifthSixWord_forward]
  exact generatedFifthSixSchreier_certificate k i j

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
