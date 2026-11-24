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
# The actual zero isomorphisms of independent category universe lifts

The existing mapZeroObject isomorphisms agree with the category owner's
canonical zero isomorphisms. The unit/counit triangles use the same original
maps and the actual chosen zero objects. No equality between different chosen
zero objects, category witness or topological transport witness is required.
-/

public section

noncomputable section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

universe uR uM uObj uHom

namespace FGProjectiveCat.CategoryUniverseLift

variable (R : Type uR) [Ring R]

/-- The usual forward zero comparison is the same canonical lifted zero iso. -/
theorem upFunctorMapZeroObject :
    (upFunctor.{uR, uM, uObj, uHom} R).mapZeroObject =
      upZeroIso.{uR, uM, uObj, uHom} R := by
  apply Iso.ext
  exact (isZero_zero (category.{uR, uM, uObj, uHom} R)).eq_of_tgt _ _

/-- The usual inverse zero comparison is the same canonical descending zero iso. -/
theorem downFunctorMapZeroObject :
    (downFunctor.{uR, uM, uObj, uHom} R).mapZeroObject =
      downZeroIso.{uR, uM, uObj, uHom} R := by
  apply Iso.ext
  exact (isZero_zero (originalCategory.{uR, uM} R)).eq_of_tgt _ _

/-- The original unit and both actual zero comparisons form the old-zero triangle. -/
theorem unitZeroTriangle :
    (equivalence.{uR, uM, uObj, uHom} R).unitIso.hom.app
        (0 : originalCategory.{uR, uM} R) ≫
      (downFunctor.{uR, uM, uObj, uHom} R).map
        (upZeroIso.{uR, uM, uObj, uHom} R).hom ≫
      (downZeroIso.{uR, uM, uObj, uHom} R).hom =
        𝟙 (0 : originalCategory.{uR, uM} R) :=
  (isZero_zero (originalCategory.{uR, uM} R)).eq_of_src _ _

/-- The original counit is the composite of the same two actual zero comparisons. -/
theorem counitZeroTriangle :
    (upFunctor.{uR, uM, uObj, uHom} R).map
        (downZeroIso.{uR, uM, uObj, uHom} R).hom ≫
      (upZeroIso.{uR, uM, uObj, uHom} R).hom =
        (equivalence.{uR, uM, uObj, uHom} R).counitIso.hom.app
          (0 : category.{uR, uM, uObj, uHom} R) :=
  (isZero_zero (category.{uR, uM, uObj, uHom} R)).eq_of_tgt _ _

end FGProjectiveCat.CategoryUniverseLift

end
