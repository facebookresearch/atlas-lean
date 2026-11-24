/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.FixedObjectFreeAdjunction
import MathlibExt.AlgebraicTopology.SimplicialCategory.FixedObjectSmallColimits
import MathlibExt.AlgebraicTopology.SimplicialCategory.FreeScalarPaths
import MathlibExt.CategoryTheory.Category.RelativeFreePresentation
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Limits.Pi
import MathlibExt.AlgebraicTopology.SimplicialCategory.FixedObjectScalarCategories

/-!
# The actual original initial enrichment has a full scalar free presentation

The existing original free adjunction maps the actual initial Hom family
to an initial enrichment with the same object labels. Its actual initial
isomorphism supplies the full original Hom coordinate map. Thus each
scalar level is genuinely free on the original empty generator family.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite

namespace CategoryTheory.SimplicialEnrichment.FixedObjects.InitialScalarFreePresentation
open RelativeWords FixedObjectFree
variable {O : Type u}

/-- The actual pointwise initial original coefficient family. -/
def family : Families O := fun _ => ⊥_ SSet.{u}

/-- The entire original pointwise initial family has the genuine initial universal property. -/
def familyIsInitial : IsInitial (family (O := O)) :=
  IsInitial.ofUniqueHom (fun Q p => initial.to (Q p)) (fun Q f => by
    funext p
    exact initial.hom_ext (f p) (initial.to (Q p)))

/-- The actual original free initial Hom family retains the same labels. -/
abbrev object : FixedObjects O := (freeFunctor (O := O)).obj (family (O := O))

/-- This SAME original free object is genuinely initial. -/
def isInitial : IsInitial (object (O := O)) := by
  let _ : (freeFunctor (O := O)).IsLeftAdjoint := ⟨underlyingFunctor (O := O), ⟨adjunction (O := O)⟩⟩
  exact (familyIsInitial (O := O)).isInitialObj (freeFunctor (O := O)) (family (O := O))

/-- The exact original free-initial object comparison. -/
def iso : object (O := O) ≅ ⊥_ (FixedObjects O) :=
  IsInitial.uniqueUpToIso isInitial initialIsInitial

/-- Each actual original free enrichment has its literal full scalar path presentation. -/
def freePresentation (Q : SimplicialQuiver.Data O) (q : SimplexCategoryᵒᵖ) :
    FreePresentation.{u,u,u} (scalarCategory (FreeQuiver.object Q) q) where
  quiver := SimplicialQuiver.quiverAt Q q
  map p := p
  map_id _ := rfl
  map_comp _ _ := rfl
  bijective _ _ := Function.bijective_id

/-- Construct the same original initial enrichment's full scalar free presentation. -/
def presentation (q : SimplexCategoryᵒᵖ) :
    FreePresentation.{u,u,u} (scalarCategory (⊥_ (FixedObjects O)) q) where
  quiver := (freePresentation (quiver (family (O := O))) q).quiver
  map {a b} p := (homMap iso.hom a b).app q p
  map_id a := congr($(identityMap_homMap iso.hom a).app q PUnit.unit)
  map_comp {a b c} p r := congr($(compositionMap_homMap iso.hom a b c).app q (p,r))
  bijective a b := by
    let e := (evaluation a b).mapIso iso
    let eq := ((CategoryTheory.evaluation _ _).obj q).mapIso e
    exact ConcreteCategory.bijective_of_isIso eq.hom

end CategoryTheory.SimplicialEnrichment.FixedObjects.InitialScalarFreePresentation
