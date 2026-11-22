/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.LeftDecalageObjectRealizedMappingContraction
import MathlibExt.AlgebraicTopology.SimplicialSpace.LeftDecalageObjectNativeBasedContraction

/-!
# Pointwise readback of the native contraction on the original mapping fibre

The same native contraction, evaluated on the whole original diagonal
mapping parameter, projects to the standard original edge path at every
time. No Segal or fibrancy assumption is needed for this map identity.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u

open CategoryTheory CategoryTheory.Limits Topology
open scoped Simplicial

namespace SimplicialSpace.LeftDecalageObject

/-- Projecting the original realized native contraction keeps the complete standard edge path. -/
theorem nativeMappingPath_apply (W : SimplicialSpace.{u})
    (x y : (W.diagram _⦋0⦌) _⦋0⦌) (z : SSet.toTop.obj (mappingFibre W x y))
    (t : unitInterval) :
    realizedDiagonalProjection W x
        (realizedNativePointContraction W x (t, SSet.toTop.map (mappingToPathDiagonal W x y) z)) =
      mappingFibreDiagonalPathFamily W x y z (TopCat.I.homeomorph.symm t) := by
  let q := (TopCat.prodIsoProd TopCat.I.{u} (SSet.toTop.obj (mappingFibre W x y))).inv
    (TopCat.I.homeomorph.symm t, z)
  have hp : (prod.map (𝟙 TopCat.I.{u}) (SSet.toTop.map (mappingToPathDiagonal W x y))) q =
      (TopCat.prodIsoProd TopCat.I.{u}
        (SSet.toTop.obj (SSet.simplicialDiagonalFunctor.obj (diagram W x)))).inv
          (TopCat.I.homeomorph.symm t, SSet.toTop.map (mappingToPathDiagonal W x y) z) := by
    exact TopCat.prodMap_prodIso_inv_apply _ _ _
  have h := ConcreteCategory.congr_hom (realizedMappingContraction_projection W x y) q
  rw [realizedNativePointContraction_apply]
  rw [← hp]
  exact h

/-- Reversing the same actual based contraction recovers the original point-to-identity interval. -/
theorem nativeBasedContraction_reverse_apply (W : SimplicialSpace.{u})
    (x : (W.diagram _⦋0⦌) _⦋0⦌) (t : unitInterval)
    (z : SSet.toTop.obj (SSet.simplicialDiagonalFunctor.obj (diagram W x))) :
    (nativeBasedContraction W x).homotopy.symm (t, z) =
      realizedNativePointContraction W x (t, z) := by
  change (realizedNativePointContraction W x).symm.symm (t, z) = _
  rw [ContinuousMap.Homotopy.symm_symm]

end SimplicialSpace.LeftDecalageObject
