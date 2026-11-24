/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

import MathlibExt.CategoryTheory.ExactCategory.Equivalence

/-!
# Exact-category equivalence transport tests

The tests pin exact, admissible-mono, and admissible-epi membership, the
split sequence, and the transported pushout/pullback fields.  The construction
is installed only locally.
-/

noncomputable section

open CategoryTheory Limits Preadditive

namespace MathlibExtTest.ExactCategoryEquivalence

universe v u

variable (C : Type u) [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]

section OpOp

local instance opOpEquivalenceFunctorAdditive :
    (opOpEquivalence C).functor.Additive where
  map_add := by
    intro X Y f g
    rfl

local instance transportedOpOp : ExactCategory Cᵒᵖᵒᵖ :=
  ExactCategory.ofEquivalence (opOpEquivalence C)

example (S : ShortComplex Cᵒᵖᵒᵖ) :
    ExactCategory.IsAdmissibleExact S ↔
      ExactCategory.IsAdmissibleExact
        (S.map (opOpEquivalence C).functor) :=
  ExactCategory.ofEquivalence_isAdmissibleExact_iff
    (opOpEquivalence C) S

example {X Y : Cᵒᵖᵒᵖ} (f : X ⟶ Y) :
    ExactCategory.IsAdmissibleMono f ↔
      ExactCategory.IsAdmissibleMono
        ((opOpEquivalence C).functor.map f) :=
  ExactCategory.ofEquivalence_isAdmissibleMono_iff
    (opOpEquivalence C) f

example {X Y : Cᵒᵖᵒᵖ} (f : X ⟶ Y) :
    ExactCategory.IsAdmissibleEpi f ↔
      ExactCategory.IsAdmissibleEpi
        ((opOpEquivalence C).functor.map f) :=
  ExactCategory.ofEquivalence_isAdmissibleEpi_iff
    (opOpEquivalence C) f

example (X Y : Cᵒᵖᵒᵖ) :
    ExactCategory.IsAdmissibleExact
      (ShortComplex.mk (biprod.inl : X ⟶ X ⊞ Y) biprod.snd (by simp)) :=
  ExactCategory.isAdmissibleExact_split X Y

example {X Y X' : Cᵒᵖᵒᵖ} (i : X ⟶ Y)
    (hi : ExactCategory.IsAdmissibleMono i) (f : X ⟶ X') :
    ∃ (P : Cᵒᵖᵒᵖ) (inl : X' ⟶ P) (inr : Y ⟶ P),
      IsPushout f i inl inr ∧ ExactCategory.IsAdmissibleMono inl :=
  ExactCategory.admissibleMono_pushout X Y i hi X' f

example {Y Z Z' : Cᵒᵖᵒᵖ} (p : Y ⟶ Z)
    (hp : ExactCategory.IsAdmissibleEpi p) (g : Z' ⟶ Z) :
    ∃ (P : Cᵒᵖᵒᵖ) (fst : P ⟶ Z') (snd : P ⟶ Y),
      IsPullback fst snd g p ∧ ExactCategory.IsAdmissibleEpi fst :=
  ExactCategory.admissibleEpi_pullback Y Z p hp Z' g

end OpOp

end MathlibExtTest.ExactCategoryEquivalence

end
