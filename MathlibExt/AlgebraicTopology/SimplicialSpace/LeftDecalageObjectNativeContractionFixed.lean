/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.LeftDecalageObjectNativeHomotopyFaces
import MathlibExt.AlgebraicTopology.SimplicialSpace.LeftDecalageObjectNativeContractionEndpoints
import MathlibExt.AlgebraicTopology.SimplicialSet.SimplicialObjectHomotopyDiagonalFixed

/-!
# The original path diagonal contraction fixes its original section

Every original contraction face fixes the same retained section. The
actual diagonal interval contraction therefore fixes that whole section,
including every original interval simplex and original fixed object.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u

open CategoryTheory MonoidalCategory Opposite
open scoped Simplicial

namespace SimplicialSpace.LeftDecalageObject

/-- The actual native diagonal interval contraction fixes its entire original retained section. -/
theorem nativeDiagonalContraction_fixed_section (W : SimplicialSpace.{u})
    (x : (W.diagram _⦋0⦌) _⦋0⦌) :
    (SSet.simplicialDiagonalFunctor.map (nativeSection W x) ⊗ₘ 𝟙 (Δ[1] : SSet.{u})) ≫
        (nativeDiagonalContraction W x).h =
      CartesianMonoidalCategory.fst
        (SSet.simplicialDiagonalFunctor.obj ((SimplicialObject.const SSet.{u}).obj (Δ[0] : SSet.{u})))
        (Δ[1] : SSet.{u}) ≫ SSet.simplicialDiagonalFunctor.map (nativeSection W x) := by
  have h := SimplicialObject.Homotopy.diagonalHomotopyMap_fixed_section
    (extraDegeneracy W x).homotopy (nativeSection W x) (by
      change nativeSection W x ≫ 𝟙 (diagram W x) = nativeSection W x
      exact Category.comp_id _)
    (fun n i => nativeSection_homotopyFace W x n i)
  exact h

end SimplicialSpace.LeftDecalageObject
