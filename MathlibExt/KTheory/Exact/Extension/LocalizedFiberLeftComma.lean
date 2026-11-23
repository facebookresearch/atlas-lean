/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Exact.Extension.LocalizedBaseChange
public import MathlibExt.CategoryTheory.FiberedCategory.FiberedComma

/-!
# The original localized pullback maps into the left-comma transition

The component is the stock Cartesian lift of the given original Quillen arrow.
Its comma square is the full HomLift factor equation, with both stored fiber
object equalities. Naturality is the actual base-change map factor equation.
The original localized objects, denominators, stabilizers and Quillen spans remain.
-/

universe u v

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory
open CategoryTheory.MonoidalActionCategory
open scoped CategoryTheory.Limits.CoreBiprodMonoidal

namespace AlgebraicKTheory.LocalizedBaseChange

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]

attribute [local instance] ExtensionCategory.leftSumAction
attribute [local instance] FixedTargetExtension.leftSumAction
attribute [local instance] MonoidalActionCategory.diagonalAction
attribute [local instance] ExtensionCategory.localizedTarget_isFibered

/-- The original chosen lift is a morphism in the actual left comma after base change. -/
def baseChangeToStructuredArrowComponent {R S : QuillenQ C} (f : R ⟶ S)
    (a : Functor.Fiber (projection (C := C)) S) :
    ((baseChangeFunctor f ⋙
      Functor.fiberToStructuredArrow (p := projection (C := C)) R).obj a) ⟶
      ((Functor.fiberToStructuredArrow (p := projection (C := C)) S ⋙
        StructuredArrow.map (T := projection (C := C)) f).obj a) :=
  StructuredArrow.homMk (baseChangeLift f a) (by
    let _ : Functor.IsHomLift (projection (C := C)) f (baseChangeLift f a) := by
      change Functor.IsHomLift (projection (C := C)) f
        (Functor.IsPreFibered.pullbackMap (p := projection (C := C)) a.property f)
      infer_instance
    have hMap : (projection (C := C)).map (baseChangeLift f a) =
        eqToHom (baseChangeObject f a).property ≫ f ≫ eqToHom a.property.symm :=
      IsHomLift.fac' (projection (C := C)) f (baseChangeLift f a)
    change eqToHom (baseChangeObject f a).property.symm ≫
      (projection (C := C)).map (baseChangeLift f a) = f ≫ eqToHom a.property.symm
    calc
      eqToHom (baseChangeObject f a).property.symm ≫
          (projection (C := C)).map (baseChangeLift f a) =
        eqToHom (baseChangeObject f a).property.symm ≫
          (eqToHom (baseChangeObject f a).property ≫ f ≫ eqToHom a.property.symm) :=
        congrArg (eqToHom (baseChangeObject f a).property.symm ≫ ·) hMap
      _ = (eqToHom (baseChangeObject f a).property.symm ≫
          eqToHom (baseChangeObject f a).property) ≫ (f ≫ eqToHom a.property.symm) :=
        (Category.assoc _ _ _).symm
      _ = f ≫ eqToHom a.property.symm := by
        simp only [eqToHom_trans, eqToHom_refl, Category.id_comp])

/-- The exact pullback-to-comma comparison is natural on all original fiber morphisms. -/
def baseChangeToStructuredArrow {R S : QuillenQ C} (f : R ⟶ S) :
    baseChangeFunctor f ⋙
      Functor.fiberToStructuredArrow (p := projection (C := C)) R ⟶
    Functor.fiberToStructuredArrow (p := projection (C := C)) S ⋙
      StructuredArrow.map (T := projection (C := C)) f where
  app a := baseChangeToStructuredArrowComponent f a
  naturality {a b} phi := by
    apply StructuredArrow.hom_ext
    change (baseChangeMap f phi).val ≫ baseChangeLift f b =
      baseChangeLift f a ≫ phi.val
    exact baseChangeMap_fac f phi

/-- The full total-arrow coordinate is the original chosen Cartesian lift. -/
theorem baseChangeToStructuredArrow_app_right {R S : QuillenQ C} (f : R ⟶ S)
    (a : Functor.Fiber (projection (C := C)) S) :
    ((baseChangeToStructuredArrow f).app a).right = baseChangeLift f a := rfl

end AlgebraicKTheory.LocalizedBaseChange

end
