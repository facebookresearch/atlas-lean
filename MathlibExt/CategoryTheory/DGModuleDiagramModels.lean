/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.CategoryTheory.DGModuleConeShiftModels
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic

/-!
# Whole DG-module diagram replacements and normalized comparisons

Projective cofibrancy is tested in the actual diagram category, against
natural transformations which are trivial module fibrations at every
index. A replacement is an actual augmented diagram with that whole
lifting property; pointwise module cofibrancy is not substituted for it.

A comparison is one native natural transformation of the whole diagrams,
with every component fixed by the supplied bar/counit/duality formula.
Its naturality retains all diagram edges and composition coherence.

References: Hovey, Model Categories, §5; Brav--Dyckerhoff,
arXiv:1606.00619v1, diagrams4.9 and6.5--6.7.
-/

@[expose] public noncomputable section

namespace MathlibExt.CategoryTheory.DGModuleDiagramModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open MathlibExt.CategoryTheory.DGModelContracts
open MathlibExt.CategoryTheory.DGQuasiFunctorModels

universe u v w
variable {k : Type u} [CommRing k] {C : DGCat k}
variable {J : Type v} [Category.{w} J]

/-- The actual projective lifting property of a whole DG-module diagram. -/
def IsProjectivelyCofibrant (D : J ⥤ RightModule k C) : Prop :=
  ∀ (U V : J ⥤ RightModule k C) (p : U ⟶ V),
    (∀ j : J, IsModuleTrivialFibration (p.app j)) →
    ∀ f : D ⟶ V, ∃ g : D ⟶ U, g ≫ p = f

/-- A whole-diagram replacement retains its actual augmentation and component trivial fibrations. -/
structure ProjectiveDiagramReplacement (D : J ⥤ RightModule k C) where
  diagram : J ⥤ RightModule k C
  augmentation : diagram ⟶ D
  trivial : ∀ j : J, IsModuleTrivialFibration (augmentation.app j)
  cofibrant : IsProjectivelyCofibrant diagram

/-- A joint comparison fixes every native component while keeping all diagram naturality. -/
structure NormalizedDiagramComparison {D E : J ⥤ RightModule k C}
    (R : ProjectiveDiagramReplacement D)
    (component : ∀ j : J, R.diagram.obj j ⟶ E.obj j) where
  map : R.diagram ⟶ E
  component_eq : ∀ j : J, map.app j = component j

/-- The actual component map of the one joint comparison, retaining its source augmentation. -/
def componentMap {D E : J ⥤ RightModule k C} {R : ProjectiveDiagramReplacement D}
    {component : ∀ j : J, R.diagram.obj j ⟶ E.obj j}
    (M : NormalizedDiagramComparison R component) (j : J) : R.diagram.obj j ⟶ E.obj j :=
  M.map.app j

end MathlibExt.CategoryTheory.DGModuleDiagramModels
