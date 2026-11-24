/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
  Author: @toskua, Avocado
-/
module

public import MathlibExt.KTheory.Ring.K2.StableSteinbergFiniteWeylPermutationTrivial

@[expose] public section

noncomputable section

set_option autoImplicit false

open Matrix.GeneralLinearGroup

universe u

namespace AlgebraicKTheory.StableSteinberg

example (F : Type u) [Field F] :
    evalFiniteWeylWord ([] : FiniteWeylWord F (Fin 0)) = 1 := by
  simp

example (F : Type u) [Field F] :
    evalFiniteWeylWordInStableE ([] : FiniteWeylWord F (Fin 1)) = 1 := by
  simp

example {F : Type u} [Field F] {n : ℕ}
    (letter : WeylLetter F (Fin n)) :
    toStableE (evalFiniteWeylWord [letter]) =
      evalFiniteWeylWordInStableE [letter] := by
  exact toStableE_evalFiniteWeylWord [letter]

example {F : Type u} [Field F] {n : ℕ}
    (word₁ word₂ : FiniteWeylWord F (Fin n)) :
    evalFiniteWeylWord (word₁ ++ word₂) =
      evalFiniteWeylWord word₁ * evalFiniteWeylWord word₂ := by
  exact evalFiniteWeylWord_append word₁ word₂

example {F K : Type u} [Field F] [Field K]
    (f : F →+* K) {n : ℕ} (word : FiniteWeylWord F (Fin n)) :
    AlgebraicKTheory.StableSteinberg.mapRingHom f
        (evalFiniteWeylWord word) =
      evalFiniteWeylWord (FiniteWeylWord.mapRingHom f word) := by
  simp

example :
    evalFiniteWeylWordInStableE
        ([] : FiniteWeylWord (ZMod 2) (Fin 1)) = 1 := by
  simp

end AlgebraicKTheory.StableSteinberg

namespace Matrix.GeneralLinearGroup

example {F : Type u} [Field F] {m n : ℕ}
    (a b : Fin m → ℕ) (ha : ∀ k, a k < n) (hb : ∀ k, b k < n)
    (hab : ∀ k, a k ≠ b k) (units : Fin m → Fˣ) :
    bruhatMiddle
        (List.prod (List.ofFn fun k =>
          weylSLUnit (⟨a k, ha k⟩ : Fin n) (⟨b k, hb k⟩ : Fin n)
            (fun h => hab k (congrArg Fin.val h)) (units k))) =
      List.prod (List.ofFn fun k =>
        weylMonomialSLUnit (⟨a k, ha k⟩ : Fin n)
          (⟨b k, hb k⟩ : Fin n)
          (fun h => hab k (congrArg Fin.val h)) (units k)) := by
  exact finiteWeyl_list_bruhatMiddle_eq
    (fun k => (⟨a k, ha k⟩ : Fin n))
    (fun k => (⟨b k, hb k⟩ : Fin n))
    (fun k h => hab k (congrArg Fin.val h)) units

example {F : Type u} [Field F] {m n : ℕ}
    (a b : Fin m → ℕ) (ha : ∀ k, a k < n) (hb : ∀ k, b k < n)
    (hab : ∀ k, a k ≠ b k) (units : Fin m → Fˣ)
    (hmono : List.prod (List.ofFn fun k =>
      weylMonomialSLUnit (⟨a k, ha k⟩ : Fin n)
        (⟨b k, hb k⟩ : Fin n)
        (fun h => hab k (congrArg Fin.val h)) (units k)) = 1) :
    FiniteWeylWord.permEval
        (FiniteWeylWord.ofBoundedNat a b ha hb hab units) = 1 := by
  apply FiniteWeylWord.permEval_eq_one_of_monomialSLEval_eq_one
  rw [FiniteWeylWord.monomialSLEval_ofBoundedNat]
  exact hmono

end Matrix.GeneralLinearGroup

end
