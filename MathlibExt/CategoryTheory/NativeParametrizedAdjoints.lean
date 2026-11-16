/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.CategoryTheory.Adjunction.Parametrized
public import Mathlib.CategoryTheory.Adjunction.Mates

/-!
# The native right-adjoint bifunctor from a fixed left-adjoint bifunctor

The right-adjoint objects are the original native chosen adjoints.
Their parameter maps are the native conjugate transformations. Native
identity/composition and unit-mate laws prove the full parametrized
adjunction, retaining contravariance in the parameter.

Source: Mathlib56a005855ea17e0b0958f73ec801ae140b0a1679,
CategoryTheory/Adjunction/Mates and Parametrized, Apache2.0,
Joël Riou and the Mathlib contributors. This is a specialization of
those completed native constructors and laws.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.CategoryTheory.NativeParametrizedAdjoints

open _root_.CategoryTheory _root_.Opposite

universe uA uB uC vA vB vC

variable {A : Type uA} {B : Type uB} {C : Type uC}
  [Category.{vA} A] [Category.{vB} B] [Category.{vC} C]
  (F : A ⥤ B ⥤ C) [∀ a : A, (F.obj a).IsLeftAdjoint]

/-- The actual right-adjoint bifunctor, with native mate maps in the contravariant parameter. -/
def rightAdjointBifunctor : Aᵒᵖ ⥤ C ⥤ B where
  obj a := (F.obj a.unop).rightAdjoint
  map {a b} f :=
    conjugateEquiv (Adjunction.ofIsLeftAdjoint (F.obj a.unop))
      (Adjunction.ofIsLeftAdjoint (F.obj b.unop)) (F.map f.unop)
  map_id a := by
    rw [unop_id, F.map_id, conjugateEquiv_id]
  map_comp {a b c} f g := by
    change conjugateEquiv (Adjunction.ofIsLeftAdjoint (F.obj a.unop))
        (Adjunction.ofIsLeftAdjoint (F.obj c.unop)) (F.map (g.unop ≫ f.unop)) = _
    rw [F.map_comp]
    exact (conjugateEquiv_comp (Adjunction.ofIsLeftAdjoint (F.obj a.unop))
      (Adjunction.ofIsLeftAdjoint (F.obj b.unop)) (Adjunction.ofIsLeftAdjoint (F.obj c.unop))
      (F.map f.unop) (F.map g.unop)).symm

/-- The complete native parametrized adjunction of the original fixed bifunctor. -/
def nativeParametrizedAdjunction : F ⊣₂ rightAdjointBifunctor F where
  adj a := Adjunction.ofIsLeftAdjoint (F.obj a)
  unit_whiskerRight_map {a b} f := by
    ext x
    exact (unit_conjugateEquiv (Adjunction.ofIsLeftAdjoint (F.obj b))
      (Adjunction.ofIsLeftAdjoint (F.obj a)) (F.map f) x).symm

end MathlibExt.CategoryTheory.NativeParametrizedAdjoints
