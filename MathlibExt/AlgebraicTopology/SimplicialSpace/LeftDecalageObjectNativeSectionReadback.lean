/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.LeftDecalageObjectNativeContraction

/-!
# The original whole fixed-object section readback

Every original outer degree of the retained section is the same original
identity edge followed by the original shifted constant operator. Its
fixed-object projection remains the actual point coefficient.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u

open CategoryTheory Opposite
open scoped Simplicial

namespace SimplicialSpace.LeftDecalageObject

set_option backward.isDefEq.respectTransparency false in
/-- Every retained original section degree has the same original whole shifted identity-edge map. -/
theorem nativeSection_fst (W : SimplicialSpace.{u}) (x : (W.diagram _⦋0⦌) _⦋0⦌)
    (n : SimplexCategoryᵒᵖ) :
    (nativeSection W x).app n ≫ (toDecalage W x).app n =
      SSet.yonedaEquiv.symm x ≫ W.diagram.map
        (SimplicialObject.LeftDecalage.ordinal.map (SimplexCategory.isTerminalZero.from n.unop) ≫
          SimplexCategory.σ (0 : Fin 1)).op := by
  change (extraDegeneracy W x).s' ≫
    (diagram W x).map (SimplexCategory.isTerminalZero.from n.unop).op ≫
      (toDecalage W x).app n = _
  rw [← sectionZero_eq_extraDegeneracy_section]
  change sectionZero W x ≫ ((diagram W x).map (SimplexCategory.isTerminalZero.from n.unop).op ≫
    (toDecalage W x).app n) = _
  rw [(toDecalage W x).naturality, ← Category.assoc]
  rw [sectionZero_fst, Category.assoc]
  change SSet.yonedaEquiv.symm x ≫ W.diagram.map (SimplexCategory.σ (0 : Fin 1)).op ≫
    W.diagram.map (SimplicialObject.LeftDecalage.ordinal.map
      (SimplexCategory.isTerminalZero.from n.unop)).op = _
  rw [← W.diagram.map_comp, ← op_comp]

end SimplicialSpace.LeftDecalageObject
