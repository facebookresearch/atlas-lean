/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentOutsideFaceAlgebra

/-!
# The original enriched identity in an actual supplied outside face

The genuine outside-face Hom isomorphism transports the supplied face
functor's whole identity to the same individual original vertex.
-/

noncomputable section
universe u
open CategoryTheory MonoidalCategory
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OutsideFaceIdentity
open SimplicialEnrichment
variable {C : Carrier.{u}} {n : ℕ} {i : Fin (n + 3)}
  (f : (Λ[n + 2, i] : SSet.{u}) ⟶ coherentNerveFunctor.obj C)

/-- The entire original outside-face Hom extraction preserves the actual enriched identity
at its supplied vertex. -/
theorem faceMap_id (j : Fin (n + 3)) (hj : j ≠ i) (a' : ULift.{u} (Fin (n + 2)))
    (h : (ULift.up j : ULift.{u} (Fin (n + 3))) < (OrdinalFace.embedding j) a' ∨
      (OrdinalFace.embedding j) a' < ULift.up j)
    {a : Fin (n + 3)} (ha : j.succAbove a'.down = a) :
    eId SSet.{u} (SimplicialThickening.mk (ULift.up.{u} a)) ≫
      HornOutsideIntervals.faceMap f j hj a' a' h ha ha = eId SSet.{u} (HornFaces.object f a) := by
  let _ : IsIso ((coherentSimplexMap (SimplexCategory.δ j)).map (.mk a') (.mk a')) :=
    OutsideFaceAlgebra.outside_isIso j a' a' h
  rw [OutsideFaceAlgebra.faceMap_eq_transport f j hj a' a' h ha ha]
  exact HomTransportEndpoints.map_id (coherentSimplexMap (SimplexCategory.δ j))
    (HornFaces.faceFunctor f j hj)
    (SimplicialThickening.mk a')
    (congrArg (fun a : Fin (n + 3) => SimplicialThickening.mk (ULift.up.{u} a)) ha)
    ((HornFaces.faceFunctor_obj f j hj (.mk a')).trans (congrArg (HornFaces.object f) ha))

end CategoryTheory.CoherentRealization.OutsideFaceIdentity
