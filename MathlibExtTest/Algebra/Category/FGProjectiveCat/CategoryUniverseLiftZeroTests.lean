/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.Algebra.Category.FGProjectiveCat.CategoryUniverseLiftZero

public section

noncomputable section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject
open FGProjectiveCat.CategoryUniverseLift

universe uR uM uObj uHom

variable (R : Type uR) [Ring R]

example : (upFunctor.{uR, uM, uObj, uHom} R).mapZeroObject =
    upZeroIso.{uR, uM, uObj, uHom} R :=
  upFunctorMapZeroObject.{uR, uM, uObj, uHom} R

example : (downFunctor.{uR, uM, uObj, uHom} R).mapZeroObject =
    downZeroIso.{uR, uM, uObj, uHom} R :=
  downFunctorMapZeroObject.{uR, uM, uObj, uHom} R

example : (equivalence.{uR, uM, uObj, uHom} R).unitIso.hom.app
      (0 : originalCategory.{uR, uM} R) ≫
    (downFunctor.{uR, uM, uObj, uHom} R).map
      (upZeroIso.{uR, uM, uObj, uHom} R).hom ≫
    (downZeroIso.{uR, uM, uObj, uHom} R).hom =
      𝟙 (0 : originalCategory.{uR, uM} R) :=
  unitZeroTriangle.{uR, uM, uObj, uHom} R

example : (upFunctor.{uR, uM, uObj, uHom} R).map
      (downZeroIso.{uR, uM, uObj, uHom} R).hom ≫
    (upZeroIso.{uR, uM, uObj, uHom} R).hom =
      (equivalence.{uR, uM, uObj, uHom} R).counitIso.hom.app
        (0 : category.{uR, uM, uObj, uHom} R) :=
  counitZeroTriangle.{uR, uM, uObj, uHom} R

end
