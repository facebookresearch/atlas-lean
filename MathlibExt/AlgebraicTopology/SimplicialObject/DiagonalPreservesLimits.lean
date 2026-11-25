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

public import MathlibExt.AlgebraicTopology.SimplicialObject.Diagonal

import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory

/-!
# Limits preserved by the simplicial diagonal

The diagonal of a simplicial object in simplicial objects preserves any
shape of limits already present in the coefficient category. This is the
generic composite of the two equivalences `flipFunctor` and
`Functor.uncurry` with precomposition along `Functor.diag`.
-/

@[expose] public section

open CategoryTheory Limits

universe w' w v u

namespace CategoryTheory.SimplicialObject

variable (C : Type u) [Category.{v} C]

/-- The simplicial diagonal preserves every shape of limits present in the
coefficient category. -/
noncomputable instance diagonalFunctor_preservesLimitsOfShape
    (J : Type w) [Category.{w'} J] [HasLimitsOfShape J C] :
    PreservesLimitsOfShape J (diagonalFunctor C) := by
  let _ : (flipFunctor SimplexCategoryᵒᵖ SimplexCategoryᵒᵖ C).IsEquivalence :=
    (Functor.flipping (C := SimplexCategoryᵒᵖ) (D := SimplexCategoryᵒᵖ)
      (E := C)).isEquivalence_functor
  let _ : (Functor.uncurry :
      (SimplexCategoryᵒᵖ ⥤ SimplexCategoryᵒᵖ ⥤ C) ⥤
        SimplexCategoryᵒᵖ × SimplexCategoryᵒᵖ ⥤ C).IsEquivalence :=
    (Functor.currying (C := SimplexCategoryᵒᵖ) (D := SimplexCategoryᵒᵖ)
      (E := C)).isEquivalence_functor
  unfold diagonalFunctor
  infer_instance

end CategoryTheory.SimplicialObject
