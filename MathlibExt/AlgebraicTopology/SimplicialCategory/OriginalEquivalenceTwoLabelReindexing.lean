/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.ComponentCategoryReindexing
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalWalkingArrowFreeSingleHomIso
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalEquivalenceArrowCoreResolution
import Mathlib.CategoryTheory.Functor.ReflectsIso.Basic

/-!
# The same original equivalence on two labels in an independent object universe

The existing generic enrichment reindexing retains all original Homs,
identities and composition at the two supplied original images. Its
projection has the literal supplied object function and identity Hom
maps, including coincident images. The actual fully faithful component
projection reflects the original equivalence vertex. Its genuine core
resolution retains that SAME full forward coefficient.
-/

noncomputable section
universe u v
open CategoryTheory MonoidalCategory Opposite
open scoped Simplicial

namespace CategoryTheory.SimplicialEnrichment.OriginalEquivalenceTwoLabelReindexing
open FixedObjects OriginalWalkingArrowFreeSingleHomIso
variable {C : Type v} [EnrichedCategory SSet.{u} C] (a : walking.{u} → C)

/-- The full original enrichment at the supplied two images, with an independent target-object universe. -/
def object : Carrier.{u} := by
  let _ : EnrichedCategory SSet.{u} walking.{u} := EnrichedCategory.reindex SSet.{u} a
  exact SimplicialEnrichment.of walking.{u}

/-- The same complete original projection, with exactly the supplied object function and identity Homs. -/
def projection : EnrichedFunctor SSet.{u} (object a) C :=
  EnrichedCategory.reindexProjection SSet.{u} a

/-- Every original full projected Hom is the literal identity at its two original image objects. -/
theorem projection_hom (x y : walking.{u}) : (projection a).map x y = 𝟙 _ := rfl

/-- Each of the two original labels retains exactly its supplied original object image. -/
theorem projection_obj (x : walking.{u}) : (projection a).obj x = a x := rfl

variable (e : (a (BergnerTwoObject.source (𝟙_ SSet.{u})) ⟶[SSet.{u}]
  a (BergnerTwoObject.target (𝟙_ SSet.{u}))) _⦋0⦌)

/-- The SAME original forward vertex, with its actual original coefficient and two labels unchanged. -/
abbrev forwardVertex : (a (BergnerTwoObject.source (𝟙_ SSet.{u})) ⟶[SSet.{u}]
    a (BergnerTwoObject.target (𝟙_ SSet.{u}))) _⦋0⦌ := e

/-- The actual fully faithful component projection reflects the SAME supplied original equivalence. -/
theorem forward_isIso (he : IsIso (ComponentCategory.arrowOf C e)) :
    IsIso (ComponentCategory.arrowOf (object a) (forwardVertex a e)) := by
  let _ : EnrichedCategory SSet.{u} walking.{u} := EnrichedCategory.reindex SSet.{u} a
  let F := ComponentCategory.mapFunctor (projection a)
  let _ : F.ReflectsIsomorphisms :=
    (ComponentCategory.reindexProjectionFullyFaithful a).reflectsIsomorphisms
  have hmap : F.map (ComponentCategory.arrowOf (object a) (forwardVertex a e)) =
      ComponentCategory.arrowOf C e := by
    change SSet.mapπ₀ (𝟙 _) (SSet.π₀.mk e) = SSet.π₀.mk e
    exact SSet.mapπ₀_id_apply _
  let _ : IsIso (F.map (ComponentCategory.arrowOf (object a) (forwardVertex a e))) :=
    (congrArg IsIso hmap).mpr he
  exact isIso_of_reflects_iso _ F

/-- The SAME actual full original core resolution on these original two labels. -/
abbrev resolvedFixedObject : FixedObjects walking.{u} :=
  ComponentEquivalenceCore.resolvedFixedObject (object a)

/-- Lift the full original free arrow through the SAME genuine original boundary core resolution. -/
def toResolution (he : IsIso (ComponentCategory.arrowOf C e)) :
    free.{u} ⟶ resolvedFixedObject a :=
  OriginalEquivalenceArrowCoreResolution.toResolution (C := object a)
    (BergnerTwoObject.source (𝟙_ SSet.{u}))
    (BergnerTwoObject.target (𝟙_ SSet.{u})) (forwardVertex a e) (forward_isIso a e he)

/-- The original complete forward coefficient survives the actual boundary projection and core inclusion. -/
theorem generator_original (he : IsIso (ComponentCategory.arrowOf C e)) :
    FreeSingleHom.generator (BergnerTwoObject.source (𝟙_ SSet.{u}))
      (BergnerTwoObject.target (𝟙_ SSet.{u})) (𝟙_ SSet.{u}) ≫
      homMap (toResolution a e he) (BergnerTwoObject.source (𝟙_ SSet.{u}))
        (BergnerTwoObject.target (𝟙_ SSet.{u})) ≫
      homMap (ComponentEquivalenceCore.resolutionRight (object a))
        (BergnerTwoObject.source (𝟙_ SSet.{u})) (BergnerTwoObject.target (𝟙_ SSet.{u})) ≫
      ComponentEquivalenceCore.inclusionHom (object a)
        (BergnerTwoObject.source (𝟙_ SSet.{u})) (BergnerTwoObject.target (𝟙_ SSet.{u})) =
      (SSet.unitHomEquiv _).symm e :=
  OriginalEquivalenceArrowCoreResolution.generator_original (C := object a)
    (BergnerTwoObject.source (𝟙_ SSet.{u}))
    (BergnerTwoObject.target (𝟙_ SSet.{u})) (forwardVertex a e) (forward_isIso a e he)

end CategoryTheory.SimplicialEnrichment.OriginalEquivalenceTwoLabelReindexing
