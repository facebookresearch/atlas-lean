/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorMono
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentLetters

/-! # Packed tensor action of words

Words in the letters Xi, the four source permutation letters and extraspecial elements act on
packed tensors letter by letter.  The theorem `tensorWord_actual` binds the packed result to the
genuine tensor action `localTensorRepresentation (identWordFiber ls)`.  Sign letters are handled
separately (they are not part of a sign-free word). -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open Multiplicative

/-- The index of a source permutation letter in `monoLetter`. -/
def monoIdx (l : Fin 2 × Bool) : Fin 4 :=
  if l.1 = 0 then (if l.2 then 1 else 0) else (if l.2 then 3 else 2)

/-- `monoIdx` is a right inverse of `monoLetter`. -/
theorem monoLetter_monoIdx (l : Fin 2 × Bool) : monoLetter (monoIdx l) = l := by
  rcases l with ⟨l1, l2⟩
  fin_cases l1 <;> cases l2 <;> rfl

/-- A letter is sign-free. -/
def IdentLetter.signFree : IdentLetter → Bool
  | .sign _ _ => false
  | _ => true

/-- All letters of a word are sign-free. -/
def signFreeWord (ls : List IdentLetter) : Bool := ls.all IdentLetter.signFree

/-- The packed tensor action of one sign-free letter (sign letters act trivially here). -/
def tensorLetter (w : ℕ) : IdentLetter → List SVec → List SVec
  | .xi, X => tensorXi w X
  | .mono l, X => tensorMono w (monoIdx l) X
  | .qel g, X => tensorQ w g X
  | .sign _ _, X => X

/-- The denominator factor of one letter. -/
def letterDen : IdentLetter → ℕ
  | .xi => 16
  | _ => 1

/-- The field bound growth factor of one letter. -/
def letterGrowth : IdentLetter → ℕ
  | .xi => 256
  | _ => 1

/-- The packed tensor action of a word: the last letter acts first. -/
def tensorWord (w : ℕ) : List IdentLetter → List SVec → List SVec
  | [], X => X
  | l :: ls, X => tensorLetter w l (tensorWord w ls X)

/-- The denominator factor of a word. -/
def tensorWordDen : List IdentLetter → ℕ
  | [] => 1
  | l :: ls => letterDen l * tensorWordDen ls

/-- The field bound growth factor of a word. -/
def tensorWordGrowth : List IdentLetter → ℕ
  | [] => 1
  | l :: ls => letterGrowth l * tensorWordGrowth ls

/-- One sign-free letter: bounds and the genuine tensor action. -/
theorem tensorLetter_actual {w B : ℕ} (l : IdentLetter) (hl : l.signFree = true)
    {X : List SVec} (hX : TBnd w B X) (hB : letterGrowth l * B < 2 ^ w) (D : ℚ) :
    TBnd w (letterGrowth l * B) (tensorLetter w l X) ∧
      localTensorRepresentation l.fiber
        (generatedAxisGlobalRationalTensorReal (tensorRat w X D)) =
      generatedAxisGlobalRationalTensorReal
        (tensorRat w (tensorLetter w l X) (letterDen l * D)) := by
  cases l with
  | xi =>
    have hB' : 4 * (64 * B) < 2 ^ w := by simp only [letterGrowth] at hB; omega
    obtain ⟨h1, h2⟩ := tensorXi_spec hX hB' D
    have e : letterGrowth IdentLetter.xi * B = 4 * (64 * B) := by simp only [letterGrowth]; ring
    refine ⟨by rw [e]; exact h1, ?_⟩
    simp only [IdentLetter.fiber, tensorLetter, letterDen, Nat.cast_ofNat]
    rw [h2]
    exact generatedAxisGlobalRationalTensorXi_actual _
  | sign a ε => simp [IdentLetter.signFree] at hl
  | mono l =>
    have hB' : B < 2 ^ w := by simpa [letterGrowth] using hB
    obtain ⟨h1, h2⟩ := tensorMono_spec (monoIdx l) hX hB' D
    refine ⟨by simpa [letterGrowth, tensorLetter] using h1, ?_⟩
    simp only [IdentLetter.fiber, tensorLetter, letterDen, Nat.cast_one, one_mul]
    rw [h2, monoLetter_monoIdx]
    have h := generatedAxisGlobalRationalTensorMonomial_actual (tensorRat w X D) [l]
    simpa using h
  | qel g =>
    have hB' : B < 2 ^ w := by simpa [letterGrowth] using hB
    refine ⟨by simpa [letterGrowth, tensorLetter] using tensorQ_bnd g hX hB', ?_⟩
    simp only [IdentLetter.fiber, tensorLetter, letterDen, Nat.cast_one, one_mul]
    rw [tensorQ_rat g hX hB']
    exact generatedAxisGlobalRationalTensorQ_actual g _

/-- A sign-free word: bounds and the genuine tensor action of the whole word. -/
theorem tensorWord_actual {w B : ℕ} : ∀ (ls : List IdentLetter), signFreeWord ls = true →
    ∀ {X : List SVec}, TBnd w B X → tensorWordGrowth ls * B < 2 ^ w → ∀ (D : ℚ),
    TBnd w (tensorWordGrowth ls * B) (tensorWord w ls X) ∧
      localTensorRepresentation (identWordFiber ls)
        (generatedAxisGlobalRationalTensorReal (tensorRat w X D)) =
      generatedAxisGlobalRationalTensorReal
        (tensorRat w (tensorWord w ls X) (tensorWordDen ls * D))
  | [], _, X, hX, _, D => by
    refine ⟨by simpa [tensorWordGrowth, tensorWord] using hX, ?_⟩
    simp [identWordFiber, tensorWord, tensorWordDen]
  | l :: ls, hsf, X, hX, hB, D => by
    simp only [signFreeWord, List.all_cons, Bool.and_eq_true] at hsf
    have hpos : 0 < letterGrowth l := by cases l <;> simp [letterGrowth]
    have hB1 : tensorWordGrowth ls * B < 2 ^ w := by
      simp only [tensorWordGrowth] at hB
      calc tensorWordGrowth ls * B ≤ letterGrowth l * (tensorWordGrowth ls * B) :=
            Nat.le_mul_of_pos_left _ hpos
        _ = letterGrowth l * tensorWordGrowth ls * B := by ring
        _ < 2 ^ w := hB
    obtain ⟨h1, h2⟩ := tensorWord_actual ls hsf.2 hX hB1 D
    have hB2 : letterGrowth l * (tensorWordGrowth ls * B) < 2 ^ w := by
      simp only [tensorWordGrowth] at hB; linarith [hB]
    obtain ⟨h3, h4⟩ := tensorLetter_actual l hsf.1 h1 hB2 (tensorWordDen ls * D)
    refine ⟨by simpa [tensorWordGrowth, tensorWord, Nat.mul_assoc] using h3, ?_⟩
    have hfib : identWordFiber (l :: ls) = l.fiber * identWordFiber ls := by
      simp [identWordFiber]
    rw [hfib, map_mul, LinearEquiv.mul_apply, h2, h4]
    simp only [tensorWord, tensorWordDen, Nat.cast_mul, mul_assoc]

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
