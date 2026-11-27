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

public import MathlibExt.LinearAlgebra.Matrix.GeneralLinearGroup.FiniteWeylWord

@[expose] public section

noncomputable section

set_option autoImplicit false

open Matrix PermutationBilinearCocycle

namespace Matrix.GeneralLinearGroup

universe u

example {R : Type u} [CommRing R] {ι : Type u}
    [DecidableEq ι] [Fintype ι] (word : FiniteWeylWord R ι)
    (hmono : FiniteWeylWord.monomialSLEval word = 1) :
    FiniteWeylWord.permEval word = 1 :=
  FiniteWeylWord.permEval_eq_one_of_monomialSLEval_eq_one word hmono

example (F : Type u) [Field F] :
    FiniteWeylWord.permEval
        ([] : FiniteWeylWord F (Fin 0)) = 1 := by
  simp

example (F : Type u) [Field F] :
    FiniteWeylWord.specialLinearEval
        ([] : FiniteWeylWord F (Fin 1)) = 1 := by
  simp

example (F : Type u) [Field F]
    (letter₁ letter₂ : WeylLetter F (Fin 3)) :
    FiniteWeylWord.permEval [letter₁, letter₂] =
      letter₁.perm * letter₂.perm := by
  simp

example (F : Type u) [Field F]
    (letter₁ letter₂ : WeylLetter F (Fin 3)) :
    FiniteWeylWord.tupleEval [letter₁, letter₂] =
      letter₁.weight *
        PermutationBilinearCocycle.permute letter₁.perm letter₂.weight := by
  simp

example (F K L : Type u) [Field F] [Field K] [Field L]
    (f : F →+* K) (g : K →+* L)
    (word : FiniteWeylWord F (Fin 4)) :
    FiniteWeylWord.mapRingHom (g.comp f) word =
      FiniteWeylWord.mapRingHom g
        (FiniteWeylWord.mapRingHom f word) := by
  exact FiniteWeylWord.mapRingHom_comp f g word

example (F K : Type u) [Field F] [Field K]
    (f : F →+* K) (word : FiniteWeylWord F (Fin 4)) :
    monomialSLMap F K (Fin 4) f
        (FiniteWeylWord.monomialSLEval word) =
      FiniteWeylWord.monomialSLEval
        (FiniteWeylWord.mapRingHom f word) := by
  simp

example (F : Type u) [Field F]
    (word₁ word₂ : FiniteWeylWord F (Fin 4)) :
    FiniteWeylWord.permEval (word₁ ++ word₂) =
      FiniteWeylWord.permEval word₁ *
        FiniteWeylWord.permEval word₂ := by
  exact FiniteWeylWord.permEval_append word₁ word₂

example :
    FiniteWeylWord.specialLinearEval
        ([] : FiniteWeylWord (ZMod 2) (Fin 1)) = 1 := by
  simp

example {F : Type u} [Field F] {m n : ℕ}
    (a b : Fin m → ℕ)
    (ha ha' : ∀ k, a k < n) (hb hb' : ∀ k, b k < n)
    (hab hab' : ∀ k, a k ≠ b k) (unit : Fin m → Fˣ) :
    FiniteWeylWord.ofBoundedNat a b ha hb hab unit =
      FiniteWeylWord.ofBoundedNat a b ha' hb' hab' unit := by
  congr

end Matrix.GeneralLinearGroup

end
