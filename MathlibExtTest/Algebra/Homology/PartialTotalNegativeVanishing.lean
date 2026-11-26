/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/

module

public import MathlibExt.Algebra.Homology.PartialTotalNegativeVanishing

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Abelian C]

variable (B : HomologicalComplex₂ C (ComplexShape.down ℕ)
  (ComplexShape.down ℕ))

example (z : ℤ) (hz : z < 0) :
    IsZero (B.partialTotalCochainFiltration.obj (z : EInt)) :=
  B.isZero_partialTotalCochainFiltration_obj_of_neg z hz

example (n a b : ℤ) (hab : a ≤ b) (ha : a < 0) (hb : b < 0) :
    IsZero ((B.partialTotalSpectralObject.H n).obj
      (CategoryTheory.ComposableArrows.mk₁
        (homOfLE (show (a : EInt) ≤ (b : EInt) by simpa using hab)))) :=
  B.isZero_partialTotalSpectralObjectHObj_of_neg n a b hab ha hb

example (n : ℤ) :
    IsZero ((B.partialTotalSpectralObject.H n).obj
      (CategoryTheory.ComposableArrows.mk₁
        (homOfLE (show ((-2 : ℤ) : EInt) ≤ ((-1 : ℤ) : EInt) by simp)))) :=
  B.isZero_partialTotalSpectralObjectHObj_of_neg n (-2) (-1)
    (by omega) (by omega) (by omega)

example (k : ℤ) :
    IsZero ((B.partialTotalSpectralObject.H k).obj
      (CategoryTheory.ComposableArrows.mk₁
        (homOfLE (show (⊥ : EInt) ≤ ((-1 : ℤ) : EInt) by simp)))) :=
  B.isZero_partialTotalSpectralObjectHObj_bot_to_neg k (-1) (by omega)

example (k : ℤ) :
    IsZero ((B.partialTotalSpectralObject.H k).obj
      (CategoryTheory.ComposableArrows.mk₁
        (homOfLE (show (⊥ : EInt) ≤ ((-2 : ℤ) : EInt) by simp)))) :=
  B.isZero_partialTotalSpectralObjectHObj_bot_to_neg k (-2) (by omega)
end HomologicalComplex₂

end
