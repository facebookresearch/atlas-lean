/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveNinthExplicit
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentLetters

/-! The explicit Ninth root words in the packed identification alphabet.

Every original odd source letter except the two inverse sign letters is a word in the
identification alphabet `GeneratedAxisGlobalIdent.IdentLetter` (the inverse source Xi is the square
of Xi, since Xi has order three). Hence the explicit Ninth root words are identification words, and
a Ninth root binding follows from two identification equations stated with identification words. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open GeneratedAxisGlobalIdent
set_option backward.isDefEq.respectTransparency false

/-- The identification word of an original odd source letter; the unused inverse sign letters
`3` and `5` are sent to the empty word. -/
def generatedAxisGlobalTwelveNinthOddIdent : Fin 10 → List IdentLetter :=
  ![[.xi], [.xi, .xi], [.sign 16 0], [], [.sign 32 0], [], [.mono (0, false)], [.mono (0, true)],
    [.mono (1, false)], [.mono (1, true)]]

private theorem ninthIdent_xi_inv :
    (localFiberIntoH xiSpinLocalFiber)⁻¹ = localFiberIntoH (xiSpinLocalFiber * xiSpinLocalFiber) := by
  have h : xiSpinLocalFiber⁻¹ = xiSpinLocalFiber * xiSpinLocalFiber := by
    apply inv_eq_of_mul_eq_one_right
    simpa only [pow_succ, pow_zero, one_mul, mul_assoc] using xiSpinLocalFiber_cube
  rw [← h, map_inv]

private theorem ninthIdent0 :
    identWordLocal [IdentLetter.xi] = generatedAxisGlobalOddSourceLocalLetter 0 :=
  identWordLocal_singleton _

private theorem ninthIdent1 :
    identWordLocal [IdentLetter.xi, IdentLetter.xi] = generatedAxisGlobalOddSourceLocalLetter 1 := by
  have h : identWordLocal [IdentLetter.xi, IdentLetter.xi] =
      localFiberIntoH (xiSpinLocalFiber * xiSpinLocalFiber) := by
    simp [identWordLocal, identWordFiber, IdentLetter.fiber]
  rw [h, ← ninthIdent_xi_inv]
  rfl

private theorem ninthIdent2 :
    identWordLocal [IdentLetter.sign 16 0] = generatedAxisGlobalOddSourceLocalLetter 2 := by
  rw [identWordLocal_singleton]
  exact generatedFifth_sign_fiber_local 16 0

private theorem ninthIdent4 :
    identWordLocal [IdentLetter.sign 32 0] = generatedAxisGlobalOddSourceLocalLetter 4 := by
  rw [identWordLocal_singleton]
  exact generatedFifth_sign_fiber_local 32 0

private theorem ninthIdent6 :
    identWordLocal [IdentLetter.mono (0, false)] = generatedAxisGlobalOddSourceLocalLetter 6 := by
  rw [identWordLocal_singleton]
  rfl

private theorem ninthIdent7 :
    identWordLocal [IdentLetter.mono (0, true)] = generatedAxisGlobalOddSourceLocalLetter 7 := by
  rw [identWordLocal_singleton]
  exact map_inv localFiberIntoH _

private theorem ninthIdent8 :
    identWordLocal [IdentLetter.mono (1, false)] = generatedAxisGlobalOddSourceLocalLetter 8 := by
  rw [identWordLocal_singleton]
  rfl

private theorem ninthIdent9 :
    identWordLocal [IdentLetter.mono (1, true)] = generatedAxisGlobalOddSourceLocalLetter 9 := by
  rw [identWordLocal_singleton]
  exact map_inv localFiberIntoH _

/-- Each odd source letter other than `3` and `5` is the local element of its identification word. -/
theorem generatedAxisGlobalTwelveNinthOddIdent_local (l : Fin 10) (hl : l ≠ 3 ∧ l ≠ 5) :
    identWordLocal (generatedAxisGlobalTwelveNinthOddIdent l) =
      generatedAxisGlobalOddSourceLocalLetter l := by
  fin_cases l
  · exact ninthIdent0
  · exact ninthIdent1
  · exact ninthIdent2
  · exact (hl.1 rfl).elim
  · exact ninthIdent4
  · exact (hl.2 rfl).elim
  · exact ninthIdent6
  · exact ninthIdent7
  · exact ninthIdent8
  · exact ninthIdent9

/-- A product of odd source letters avoiding `3` and `5` is an identification word. -/
theorem generatedAxisGlobalTwelveNinthOddIdent_word (ls : List (Fin 10))
    (hls : ∀ l ∈ ls, l ≠ 3 ∧ l ≠ 5) :
    (ls.map generatedAxisGlobalOddSourceLocalLetter).prod =
      identWordLocal (ls.flatMap generatedAxisGlobalTwelveNinthOddIdent) := by
  induction ls with
  | nil => rfl
  | cons l ls ih =>
    rw [List.map_cons, List.prod_cons, List.flatMap_cons, identWordLocal_append,
      generatedAxisGlobalTwelveNinthOddIdent_local l (hls l (List.mem_cons_self ..)),
      ih (fun m hm => hls m (List.mem_cons_of_mem _ hm))]

/-- The identification words of the explicit Ninth root words. -/
def generatedAxisGlobalTwelveNinthExplicitIdent (j : Fin 8) : List IdentLetter :=
  (generatedAxisGlobalTwelveNinthExplicitLetters j).flatMap generatedAxisGlobalTwelveNinthOddIdent

/-- Each explicit Ninth root word is the local element of its identification word. -/
theorem generatedAxisGlobalTwelveNinthExplicitWord_ident (j : Fin 8) :
    generatedAxisGlobalTwelveNinthExplicitWord j =
      identWordLocal (generatedAxisGlobalTwelveNinthExplicitIdent j) :=
  generatedAxisGlobalTwelveNinthOddIdent_word _ (by fin_cases j <;> decide)

/-- A Ninth root binding from two identification equations in identification words. -/
theorem generatedAxisGlobalTwelveNinthRootBound_of_ident_eq (j : Fin 8) (kp kn : Fin 12)
    (gp gn : List IdentLetter)
    (hpos : sExtra (rhoLocal (identWordLocal (generatedAxisGlobalTwelveNinthExplicitIdent j))
      generatedNinthAxis) = rhoLocal (identWordLocal gp) (generatedAxisGlobalTwelveRepresentative kp))
    (hneg : sExtra⁻¹ (rhoLocal (identWordLocal (generatedAxisGlobalTwelveNinthExplicitIdent j))
      generatedNinthAxis) = rhoLocal (identWordLocal gn) (generatedAxisGlobalTwelveRepresentative kn)) :
    GeneratedAxisGlobalTwelveNinthRootBound j := by
  rw [← generatedAxisGlobalTwelveNinthExplicitWord_ident] at hpos hneg
  exact generatedAxisGlobalTwelveNinthRootBound_of_explicit_eq j kp kn _ _ hpos hneg

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
