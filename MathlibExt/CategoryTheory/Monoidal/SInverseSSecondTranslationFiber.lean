/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Monoidal.SInverseSTranslationDiagonalProjection
public import Mathlib.CategoryTheory.FiberedCategory.Fiber

/-!
# Second-coordinate translation on strict additive S⁻¹S fibers

Second-coordinate translation preserves the first-coordinate translation
projection on objects and arrows.  It therefore restricts to an endofunctor
of every strict fiber of that projection.

This file constructs only the strict-fiber functor and its underlying
formulas.  Comparison with core translation, comma pushforward, homology,
localization, spectral sequences, realization, and CGWH is deferred.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits ZeroObject

universe v u

namespace CategoryTheory
namespace SInverseS

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
  [HasZeroObject C] [HasBinaryBiproducts C]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Second-coordinate translation restricted to the strict fiber over `B`. -/
noncomputable def secondTranslationFiberFunctor
    (A : C) (B : Translation C) :
    (translationProjection (C := C)).Fiber B ⥤
      (translationProjection (C := C)).Fiber B where
  obj X := ⟨(translateSecondFunctor A).obj X.1, by
    change ⟨X.1.fst⟩ = B
    exact X.2⟩
  map {X Y} f := by
    let φ := (translateSecondFunctor A).map f.1
    let _ : (translationProjection (C := C)).IsHomLift
        (𝟙 B) f.1 := f.2
    let ha : (translationProjection (C := C)).obj
        ((translateSecondFunctor A).obj X.1) = B := by
      change ⟨X.1.fst⟩ = B
      exact X.2
    let hb : (translationProjection (C := C)).obj
        ((translateSecondFunctor A).obj Y.1) = B := by
      change ⟨Y.1.fst⟩ = B
      exact Y.2
    have hfac :
        (translationProjection (C := C)).map φ =
          eqToHom ha ≫ 𝟙 B ≫ eqToHom hb.symm := by
      rw [translationProjection_map_translateSecondFunctor_map]
      simpa only [Subsingleton.elim ha X.2,
        Subsingleton.elim hb Y.2] using
          IsHomLift.fac' (translationProjection (C := C)) (𝟙 B) f.1
    exact ⟨φ, IsHomLift.of_fac'
      (translationProjection (C := C)) (𝟙 B) φ ha hb hfac⟩
  map_id X := by
    apply Functor.Fiber.hom_ext
    exact (translateSecondFunctor A).map_id X.1
  map_comp f g := by
    apply Functor.Fiber.hom_ext
    exact (translateSecondFunctor A).map_comp f.1 g.1

@[simp]
theorem secondTranslationFiberFunctor_obj_val
    (A : C) (B : Translation C)
    (X : (translationProjection (C := C)).Fiber B) :
    ((secondTranslationFiberFunctor A B).obj X).1 =
      (translateSecondFunctor A).obj X.1 :=
  rfl

@[simp]
theorem secondTranslationFiberFunctor_map_val
    (A : C) (B : Translation C)
    {X Y : (translationProjection (C := C)).Fiber B} (f : X ⟶ Y) :
    ((secondTranslationFiberFunctor A B).map f).1 =
      (translateSecondFunctor A).map f.1 :=
  rfl

end SInverseS
end CategoryTheory

end
