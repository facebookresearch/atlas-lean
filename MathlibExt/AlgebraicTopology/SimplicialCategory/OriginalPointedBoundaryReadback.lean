/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalPointedCoherentHom

/-!
# The same entire original pointed boundary is its two original faces

The canonical source and target face maps determine the actual full
one-boundary map. The literal original vertices reconstruct the same
boundary without changing any original object or morphism.
-/

noncomputable section

universe u

open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OriginalPointed

/-- The entire original pointed boundary is the canonical map of its two same original endpoint vertices. -/
theorem hom_eq_boundaryOneMap (X : Category.{u}) :
    X.hom = SSet.boundaryOneMap (sourceVertex X) (targetVertex X) := by
  apply SSet.boundary.hom_ext
  intro i
  fin_cases i
  · exact ((SSet.yonedaEquiv_symm_zero (targetVertex X)).symm.trans
        (Equiv.symm_apply_apply SSet.yonedaEquiv (target X))).symm.trans
      (SSet.boundary_ι_zero_boundaryOneMap _ _).symm
  · exact ((SSet.yonedaEquiv_symm_zero (sourceVertex X)).symm.trans
        (Equiv.symm_apply_apply SSet.yonedaEquiv (source X))).symm.trans
      (SSet.boundary_ι_one_boundaryOneMap _ _).symm

end CategoryTheory.CoherentRealization.OriginalPointed
