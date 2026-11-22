/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalFixedFrontPointedDiagram
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalPointedCoherentHomFunctor
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalRightMappingSimplexTerminal

/-!
# The same original pointed zero quotient is the full original walking arrow

Both whole inverse pointed maps use the original quotient isomorphism.
Its source and target vertex images are the literal original ordinal
endpoints. No replacement of the original boundary or maps is used.
-/

noncomputable section

universe u

open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OriginalFixedFrontContraction

/-- The same original walking arrow with its literal two original ordinal endpoints. -/
def walkingArrowPointed : OriginalPointed.Category.{u} :=
  Under.mk (SSet.boundaryOneMap
    (SSet.yonedaEquiv (OriginalRawRightMapping.simplexVertex 1 0))
    (SSet.yonedaEquiv (OriginalRawRightMapping.simplexVertex 1 (Fin.last 1))))

/-- The original zero quotient forward map retains its same initial ordinal endpoint. -/
theorem zeroObjectIso_source :
    zeroObjectIso.{u}.hom.app (op ⦋0⦌) (FixedFrontCollapse.source 0) =
      SSet.yonedaEquiv (OriginalRawRightMapping.simplexVertex 1 0) := by
  exact SSet.yonedaEquiv_map _ |>.symm

/-- The original zero quotient forward map retains its same terminal ordinal endpoint. -/
theorem zeroObjectIso_target :
    zeroObjectIso.{u}.hom.app (op ⦋0⦌) (FixedFrontCollapse.target 0) =
      SSet.yonedaEquiv (OriginalRawRightMapping.simplexVertex 1 (Fin.last 1)) := by
  exact SSet.yonedaEquiv_map _ |>.symm

/-- Both actual full inverse pointed maps identify the same original zero quotient and walking arrow. -/
def pointedZeroIso : pointedObject.{u} 0 ≅ walkingArrowPointed.{u} where
  hom := Under.homMk zeroObjectIso.hom
    ((SSet.boundaryOneMap_naturality _ (FixedFrontCollapse.source 0) (FixedFrontCollapse.target 0)).trans
      (congrArg₂ SSet.boundaryOneMap zeroObjectIso_source zeroObjectIso_target))
  inv := Under.homMk zeroObjectIso.inv (by
    have h := congrArg (fun f => f ≫ zeroObjectIso.inv)
      ((SSet.boundaryOneMap_naturality zeroObjectIso.hom (FixedFrontCollapse.source 0)
        (FixedFrontCollapse.target 0)).trans
          (congrArg₂ SSet.boundaryOneMap zeroObjectIso_source zeroObjectIso_target))
    exact h.symm.trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun f => (pointedObject.{u} 0).hom ≫ f) zeroObjectIso.hom_inv_id).trans (Category.comp_id _))))
  hom_inv_id := Under.UnderMorphism.ext zeroObjectIso.hom_inv_id
  inv_hom_id := Under.UnderMorphism.ext zeroObjectIso.inv_hom_id

end CategoryTheory.CoherentRealization.OriginalFixedFrontContraction
