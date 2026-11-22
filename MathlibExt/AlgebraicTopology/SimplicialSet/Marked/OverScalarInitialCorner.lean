/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.OverCotensorBifunctor
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.OverParameterMonomorphisms
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal

/-!
# The actual fixed-scalar map is its original empty-parameter corner

The original source parameter functor preserves the actual empty scalar.
Its source map between initial parameter objects is therefore invertible.
The specified native pushout supplies an invertible whole source leg and
identifies the fixed-scalar tensor map with that original corner, with
identity target component and the same full original marked base map.
-/

noncomputable section
universe u
open CategoryTheory Limits MorphismProperty

namespace SSet.Marked

/-- The actual empty scalar parameter is initial in every original marked slice source family. -/
def overParameterEmptyIsInitial (Z : Marked.{u}) (X : Over Z) :
    IsInitial ((overParameterFunctor Z X).obj (⊥_ SSet.{u})) := by
  let G := overParameterFunctor Z X
  let _ : PreservesColimit (Functor.empty SSet.{u}) G :=
    (overParameterAdjunction Z X).leftAdjoint_preservesColimits.preservesColimitsOfShape.preservesColimit
  exact initialIsInitial.isInitialObj G _

/-- The original empty-parameter source map is an isomorphism between its actual initial marked slice objects. -/
theorem overParameterMap_empty_isIso {Z : Marked.{u}} {X Y : Over Z} (f : X ⟶ Y) :
    IsIso ((overParameterMap f).app (⊥_ SSet.{u})) := by
  let hX := overParameterEmptyIsInitial Z X
  let hY := overParameterEmptyIsInitial Z Y
  let e := hX.uniqueUpToIso hY
  have h : (overParameterMap f).app (⊥_ SSet.{u}) = e.hom := hX.hom_ext _ _
  exact h.symm ▸ (inferInstance : IsIso e.hom)

/-- The whole original empty-parameter corner source leg is actually invertible. -/
theorem overScalarInitialCorner_inr_isIso {Z : Marked.{u}} {X Y : Over Z} (f : X ⟶ Y) (K : SSet.{u}) :
    IsIso (overParameterPushout (initial.to K) f).inr := by
  let _ : IsIso (((overParameterBifunctor Z).map f).app (⊥_ SSet.{u})) := overParameterMap_empty_isIso f
  exact (overParameterPushout (initial.to K) f).isPushout.isIso_inr_of_isIso

/-- The native fixed-scalar tensor map is the original empty-parameter corner with its actual invertible
  source leg and identity target. -/
def overScalarTensorMapInitialCornerIso {Z : Marked.{u}} {X Y : Over Z} (f : X ⟶ Y) (K : SSet.{u}) :
    Arrow.mk ((overScalarTensor Z K).map f) ≅ Arrow.mk (overParameterPushoutProduct (initial.to K) f) := by
  let s := overParameterPushout (initial.to K) f
  let _ : IsIso s.inr := overScalarInitialCorner_inr_isIso f K
  exact Arrow.isoMk (@asIso _ _ _ _ s.inr (overScalarInitialCorner_inr_isIso f K)) (Iso.refl _)
    (s.inr_ι.trans (Category.comp_id _).symm)

/-- The comparison retains precisely the original pushout's whole source injection. -/
theorem overScalarTensorMapInitialCornerIso_hom_left {Z : Marked.{u}} {X Y : Over Z} (f : X ⟶ Y) (K : SSet.{u}) :
    (overScalarTensorMapInitialCornerIso f K).hom.left = (overParameterPushout (initial.to K) f).inr := rfl

/-- Its full target component is the original identity, so every original base triangle is unchanged. -/
theorem overScalarTensorMapInitialCornerIso_hom_right {Z : Marked.{u}} {X Y : Over Z} (f : X ⟶ Y) (K : SSet.{u}) :
    (overScalarTensorMapInitialCornerIso f K).hom.right = 𝟙 ((overScalarTensor Z K).obj Y) := rfl

/-- The actual fixed-scalar tensor map preserves original marked monomorphisms over any original marked base. -/
theorem overScalarTensorMap_mono {Z : Marked.{u}} {X Y : Over Z} (f : X ⟶ Y) [Mono f] (K : SSet.{u}) :
    Mono ((overScalarTensor Z K).map f) := by
  let _ : Mono (initial.to K) := inferInstance
  have h : Mono (overParameterPushoutProduct (initial.to K) f) := overParameterPushoutProduct_mono _ f
  exact ((monomorphisms (Over Z)).arrow_iso_iff (overScalarTensorMapInitialCornerIso f K)).mpr h

end SSet.Marked
