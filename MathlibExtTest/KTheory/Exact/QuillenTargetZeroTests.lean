/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.KTheory.Exact.Quillen.TargetZero

/-! # Tests for Quillen-Q morphisms into zero objects -/

@[expose] public section

noncomputable section

open CategoryTheory Limits ZeroObject
open AlgebraicKTheory

universe v u

namespace MathlibExtTest.AlgebraicKTheory.QuillenTargetZero

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]

#check QuillenQ.isIso_of_target_isZero

example {X Z : C} (f : (⟨X⟩ : QuillenQ C) ⟶ (⟨Z⟩ : QuillenQ C))
    (hZ : IsZero Z) : IsIso f :=
  QuillenQ.isIso_of_target_isZero f hZ

example {X : C} (f : (⟨X⟩ : QuillenQ C) ⟶ (⟨0⟩ : QuillenQ C)) :
    IsIso f :=
  QuillenQ.isIso_of_target_isZero f (isZero_zero C)

#print axioms QuillenQ.isIso_of_target_isZero

end MathlibExtTest.AlgebraicKTheory.QuillenTargetZero

end
