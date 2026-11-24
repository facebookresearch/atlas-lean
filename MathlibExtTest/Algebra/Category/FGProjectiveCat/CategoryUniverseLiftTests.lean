/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.Algebra.Category.FGProjectiveCat.CategoryUniverseLift

/-!
# Actual independent-category universe clients

These clients require the precise independent object/Hom sorts, the original
wrapped morphisms, all derived structures, and the actual chosen-zero isos.
The object-large and Hom-large cases do not identify those two parameters.
-/

public section

noncomputable section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject
open FGProjectiveCat.CategoryUniverseLift

universe uR uM uObj uHom

variable (R : Type uR) [Ring R]

example : Type (max (max uR uM + 1) uObj) :=
  category.{uR, uM, uObj, uHom} R

example : Category.{max (max uR uM) uHom} (category.{uR, uM, uObj, uHom} R) :=
  inferInstance

example : Preadditive (category.{uR, uM, uObj, uHom} R) := inferInstance
example : HasZeroObject (category.{uR, uM, uObj, uHom} R) := inferInstance
example : HasBinaryProducts (category.{uR, uM, uObj, uHom} R) := inferInstance
example : HasBinaryBiproducts (category.{uR, uM, uObj, uHom} R) := inferInstance
example : ExactCategory (category.{uR, uM, uObj, uHom} R) := inferInstance

example : originalCategory.{uR, uM} R ≌ category.{uR, uM, uObj, uHom} R :=
  equivalence.{uR, uM, uObj, uHom} R

example : (upFunctor.{uR, uM, uObj, uHom} R).Additive := inferInstance
example : (downFunctor.{uR, uM, uObj, uHom} R).Additive := inferInstance
example : (upFunctor.{uR, uM, uObj, uHom} R).IsExact := inferInstance
example : (downFunctor.{uR, uM, uObj, uHom} R).IsExact := inferInstance
example : (upFunctor.{uR, uM, uObj, uHom} R).Full := inferInstance
example : (downFunctor.{uR, uM, uObj, uHom} R).Faithful := inferInstance

example (X : originalCategory.{uR, uM} R) :
    (downFunctor.{uR, uM, uObj, uHom} R).obj
      ((upFunctor.{uR, uM, uObj, uHom} R).obj X) = X :=
  downUpObj.{uR, uM, uObj, uHom} R X

example (X : category.{uR, uM, uObj, uHom} R) :
    (upFunctor.{uR, uM, uObj, uHom} R).obj
      ((downFunctor.{uR, uM, uObj, uHom} R).obj X) = X :=
  upDownObj.{uR, uM, uObj, uHom} R X

example {X Y : originalCategory.{uR, uM} R} (f : X ⟶ Y) :
    (upFunctor.{uR, uM, uObj, uHom} R).map f = ULift.up f :=
  upFunctorMap.{uR, uM, uObj, uHom} R f

example {X Y : category.{uR, uM, uObj, uHom} R} (f : X ⟶ Y) :
    (downFunctor.{uR, uM, uObj, uHom} R).map f = f.down :=
  downFunctorMap.{uR, uM, uObj, uHom} R f

example (X Y : originalCategory.{uR, uM} R) :
    (upFunctor.{uR, uM, uObj, uHom} R).map (0 : X ⟶ Y) = 0 :=
  upFunctorMapZero.{uR, uM, uObj, uHom} R X Y

example : IsZero (canonicalZero.{uR, uM, uObj, uHom} R) :=
  canonicalZeroIsZero.{uR, uM, uObj, uHom} R

example : (downFunctor.{uR, uM, uObj, uHom} R).obj
    (canonicalZero.{uR, uM, uObj, uHom} R) = (0 : originalCategory.{uR, uM} R) :=
  downCanonicalZero.{uR, uM, uObj, uHom} R

example : (upFunctor.{uR, uM, uObj, uHom} R).obj (0 : originalCategory.{uR, uM} R) ≅
    (0 : category.{uR, uM, uObj, uHom} R) :=
  upZeroIso.{uR, uM, uObj, uHom} R

example : (downFunctor.{uR, uM, uObj, uHom} R).obj (0 : category.{uR, uM, uObj, uHom} R) ≅
    (0 : originalCategory.{uR, uM} R) :=
  downZeroIso.{uR, uM, uObj, uHom} R

example (S : ShortComplex (category.{uR, uM, uObj, uHom} R)) :
    ExactCategory.IsAdmissibleExact S ↔ Nonempty S.Splitting :=
  admissibleExactIffSplitting.{uR, uM, uObj, uHom} R S

example : (equivalence.{uR, uM, uObj, uHom} R).unitIso.hom.app
    (0 : originalCategory.{uR, uM} R) = 𝟙 (0 : originalCategory.{uR, uM} R) :=
  unitHomAtZero.{uR, uM, uObj, uHom} R

example : (equivalence.{uR, uM, uObj, uHom} R).counitIso.hom.app
    (0 : category.{uR, uM, uObj, uHom} R) =
      eqToHom (upDownObj.{uR, uM, uObj, uHom} R (0 : category.{uR, uM, uObj, uHom} R)) :=
  counitHomAtZero.{uR, uM, uObj, uHom} R

/- The actual object universe can be large while the Hom lift parameter stays zero. -/
example : Type (max uR uM + 2) :=
  category.{uR, uM, max uR uM + 2, 0} R

example : Category.{max uR uM}
    (category.{uR, uM, max uR uM + 2, 0} R) := inferInstance

/- The actual Hom universe can be large while the object lift parameter stays zero. -/
example : Type (max uR uM + 1) :=
  category.{uR, uM, 0, max uR uM + 3} R

example : Category.{max uR uM + 3}
    (category.{uR, uM, 0, max uR uM + 3} R) := inferInstance

end
