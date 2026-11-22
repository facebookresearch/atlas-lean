/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalNecklacePointedFunctor
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalPointedBoundaryVertices
import MathlibExt.CategoryTheory.Enriched.HomEndpointEquality

/-!
# Both same original native pointed raw-Hom coefficient directions

The literal original one-boundary vertices identify the entire native
raw Hom with its same pointed raw Hom. Every original native arrow
commutes through the actual enriched endpoint equality square.
-/

noncomputable section

universe u

open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OriginalNecklaceInput

open SSet.OriginalNecklace

/-- The same full pointed native object retains its original source vertex. -/
theorem pointedNative_sourceVertex (T : Data) :
    OriginalPointed.sourceVertex (pointedNativeFunctor.{u}.obj T) = OriginalNecklaceHom.sourceVertex T :=
  OriginalPointed.sourceVertex_boundaryOneMap _ _

/-- The same full pointed native object retains its original target vertex. -/
theorem pointedNative_targetVertex (T : Data) :
    OriginalPointed.targetVertex (pointedNativeFunctor.{u}.obj T) = OriginalNecklaceHom.targetVertex T :=
  OriginalPointed.targetVertex_boundaryOneMap _ _

/-- Both full original raw coefficient directions retain the same original native endpoints and all coefficient maps. -/
def nativePointedRawCoefficientIso : OriginalNecklaceHom.rawCoefficientFunctor.{u} ≅
    pointedNativeFunctor.{u} ⋙ OriginalPointed.homFunctor :=
  NatIso.ofComponents (fun T => eqToIso (congrArg₂
    (fun x y : T.object.{u} _⦋0⦌ => hom T.object x y)
      (pointedNative_sourceVertex T).symm (pointedNative_targetVertex T).symm)) (by
    intro T U f
    exact (EnrichedFunctor.homMap_endpoint_square (realizationMap f.map)
      (pointedNative_sourceVertex T).symm (pointedNative_targetVertex T).symm
      (pointedNative_sourceVertex U).symm (pointedNative_targetVertex U).symm
      (OriginalNecklaceHom.nativeMap_source f) (OriginalNecklaceHom.nativeMap_target f)
      (OriginalPointed.sourceVertex_map (pointedNativeFunctor.map f))
      (OriginalPointed.targetVertex_map (pointedNativeFunctor.map f))).symm)

end CategoryTheory.CoherentRealization.OriginalNecklaceInput
