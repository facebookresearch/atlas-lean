/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalPointedCoherentHom

/-!
# The original complete one-boundary has its literal original vertices

Both original boundary faces and the full original Yoneda map retain
the supplied endpoints. These equations compare the same full raw
endpoint Hom without changing any original coefficient.
-/

noncomputable section

universe u

open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OriginalPointed

/-- The same entire original endpoint boundary has the literal original source vertex. -/
theorem sourceVertex_boundaryOneMap {K : SSet.{u}} (x y : K _⦋0⦌) :
    sourceVertex (Under.mk (SSet.boundaryOneMap x y)) = x :=
  (congrArg SSet.yonedaEquiv (SSet.boundary_ι_one_boundaryOneMap x y)).trans (SSet.yonedaEquiv_const x)

/-- The same entire original endpoint boundary has the literal original target vertex. -/
theorem targetVertex_boundaryOneMap {K : SSet.{u}} (x y : K _⦋0⦌) :
    targetVertex (Under.mk (SSet.boundaryOneMap x y)) = y :=
  (congrArg SSet.yonedaEquiv (SSet.boundary_ι_zero_boundaryOneMap x y)).trans (SSet.yonedaEquiv_const y)

end CategoryTheory.CoherentRealization.OriginalPointed
