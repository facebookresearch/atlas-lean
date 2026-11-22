/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.LeftDecalageObjectNativeContractionMap

/-!
# The complete original cut formula for the native contraction cylinder

Every original interval simplex selects the original combinatorial
homotopy face at the same outer degree, evaluated at the original inner
degree. The formula retains the whole native diagonal coefficient.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u

open CategoryTheory Opposite
open scoped Simplicial

namespace SimplicialSpace.LeftDecalageObject

/-- The zero cut of the actual original contraction is its literal identity endpoint. -/
theorem nativeDiagonalContraction_cut_zero (W : SimplicialSpace.{u})
    (x : (W.diagram _⦋0⦌) _⦋0⦌) (n : ℕ)
    (z : (SSet.simplicialDiagonalFunctor.obj (diagram W x)) _⦋n⦌) :
    (nativeDiagonalContraction W x).h.app (op (SimplexCategory.mk n))
      (z, SSet.stdSimplex.objMk₁ (0 : Fin (n + 2))) = z := by
  change (((extraDegeneracy W x).homotopy.innerEvaluation (op (SimplexCategory.mk n))).toSSetHomotopyMap).app
    (op (SimplexCategory.mk n)) (z, SSet.stdSimplex.objMk₁ (0 : Fin (n + 2))) = z
  have h := SimplicialObject.Homotopy.toSSetHomotopyMap_app_objMk₁_zero
    ((extraDegeneracy W x).homotopy.innerEvaluation (op (SimplexCategory.mk n))) n
    (show ((((SimplicialObject.whiskering SSet.{u} (Type u)).obj
      (SSet.evaluation.obj (op (SimplexCategory.mk n)))).obj (diagram W x)).obj
        (op (SimplexCategory.mk n))) from z)
  exact h

/-- Every nonzero cut of the actual native cylinder is its same original homotopy face followed by its original face. -/
theorem nativeDiagonalContraction_cut_succ (W : SimplicialSpace.{u})
    (x : (W.diagram _⦋0⦌) _⦋0⦌) (n : ℕ)
    (z : (SSet.simplicialDiagonalFunctor.obj (diagram W x)) _⦋n⦌) (i : Fin (n + 1)) :
    (nativeDiagonalContraction W x).h.app (op (SimplexCategory.mk n))
      (z, SSet.stdSimplex.objMk₁ i.succ) =
      (((extraDegeneracy W x).homotopy.h i ≫ (diagram W x).δ i.succ).app
        (op (SimplexCategory.mk n))) z := by
  change (((extraDegeneracy W x).homotopy.innerEvaluation (op (SimplexCategory.mk n))).toSSetHomotopyMap).app
    (op (SimplexCategory.mk n)) (z, SSet.stdSimplex.objMk₁ i.succ) = _
  exact SimplicialObject.Homotopy.toSSetHomotopyMap_app_objMk₁_succ
    ((extraDegeneracy W x).homotopy.innerEvaluation (op (SimplexCategory.mk n))) n
    (show ((((SimplicialObject.whiskering SSet.{u} (Type u)).obj
      (SSet.evaluation.obj (op (SimplexCategory.mk n)))).obj (diagram W x)).obj
        (op (SimplexCategory.mk n))) from z) i

end SimplicialSpace.LeftDecalageObject
