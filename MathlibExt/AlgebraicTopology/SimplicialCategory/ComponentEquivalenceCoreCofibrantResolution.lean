/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.ComponentEquivalenceCoreArrowFactor
import MathlibExt.AlgebraicTopology.SimplicialCategory.FixedObjectModel
import MathlibExt.AlgebraicTopology.SimplicialCategory.EnrichedDwyerKanClasses
import Mathlib.CategoryTheory.Functor.ReflectsIso.Basic

/-!
# The SAME original component-equivalence core has an actual cofibrant resolution

The native stored free-boundary factorization of the original fixed-label
initial-to-core map supplies the SAME genuine cofibrant object and both
whole original maps. Every complete right Hom is a scalar trivial
fibration. Its actual component functor is fully faithful and the core
components are genuinely a groupoid, so the resolved source components
are a groupoid. These are constructed hypotheses for the separate
homotopical group-completion theorem; that weak outcome is not assumed.
-/

noncomputable section
universe u
open CategoryTheory Limits HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

namespace CategoryTheory.SimplicialEnrichment.ComponentEquivalenceCore
open FixedObjects

variable (C : Carrier.{u})

/-- The SAME original full core enrichment on its actual original labels. -/
def fixedTarget : FixedObjects C := by
  let _ : EnrichedCategory SSet.{u} C := enrichment C
  exact FixedObjects.of C

/-- The original fixed-label initial-to-core map retains all its actual original labels. -/
def resolutionInput : ⊥_ (FixedObjects C) ⟶ fixedTarget C := initial.to _

/-- The genuine stored original free-boundary factorization of the same initial-to-core map. -/
abbrev resolution := FreeFactorization.boundary (resolutionInput C)

/-- The SAME actual resolved fixed-label source object. -/
abbrev resolvedFixedObject : FixedObjects C := (resolution C).Z

/-- Its whole actual original varying-object carrier. -/
abbrev resolvedObject : Carrier.{u} := (resolvedFixedObject C).val

/-- The SAME actual full original boundary left leg. -/
abbrev resolutionLeft := (resolution C).i

/-- The SAME actual full original weak right map into the original core. -/
abbrev resolutionRight := (resolution C).p

/-- The entire original two factorization maps recover the actual initial-to-core input. -/
theorem resolution_fac : resolutionLeft C ≫ resolutionRight C = resolutionInput C := (resolution C).fac

/-- Every SAME complete original resolved Hom projection is a genuine scalar trivial fibration. -/
theorem resolutionRight_homs (x y : resolvedObject C) :
    Fibration ((resolutionRight C).val.map x y) ∧ SSet.realizationWeakEquivalences ((resolutionRight C).val.map x y) :=
  FreeFactorization.boundary_p_original (resolutionInput C) x y

/-- The SAME actual resolved source is genuinely cofibrant in its original fixed-object model. -/
theorem resolved_cofibrant :
    let _ : ModelCategory (FixedObjects C) := FixedObjectModel.modelCategory C
    IsCofibrant (resolvedFixedObject C) := by
  dsimp only
  let _ : ModelCategory (FixedObjects C) := FixedObjectModel.modelCategory C
  have hi : Cofibration (resolutionLeft C) :=
    (FixedObjectModel.cofibration_iff_freeBoundary (resolutionLeft C)).mpr (resolution C).hi
  have h : initial.to (resolvedFixedObject C) = resolutionLeft C := initialIsInitial.hom_ext _ _
  exact (congrArg (fun f : ⊥_ (FixedObjects C) ⟶ resolvedFixedObject C => Cofibration f) h).mpr hi

/-- The SAME original whole right map is genuinely DK weak on its full Homs and original object labels. -/
theorem resolutionRight_weak : EnrichedDwyerKan.weakEquivalences (resolutionRight C).val :=
  (EnrichedDwyerKan.fixedWeak_iff (resolutionRight C)).mpr
    ((FixedObjectModel.weakEquivalences_original_iff (resolutionRight C)).mpr
      (fun x y => (resolutionRight_homs C x y).2))

/-- The actual original resolved source component category is a genuine groupoid through the SAME full weak right
map. -/
instance resolved_component_isGroupoid : IsGroupoid (ComponentCategory.objects.{u} (resolvedObject C)) := by
  let F := ComponentCategory.mapFunctor (resolutionRight C).val
  let _ : F.ReflectsIsomorphisms :=
    (EnrichedDwyerKan.componentFullyFaithful (resolutionRight C).val (resolutionRight_weak C).1).reflectsIsomorphisms
  have : IsGroupoid (ComponentCategory.objects.{u} (fixedTarget C).val) := component_isGroupoid C
  exact isGroupoid_of_reflects_iso F

end CategoryTheory.SimplicialEnrichment.ComponentEquivalenceCore
