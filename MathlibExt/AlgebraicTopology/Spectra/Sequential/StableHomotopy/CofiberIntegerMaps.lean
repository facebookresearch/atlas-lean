/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.StabilizationKOriginalFiberComparison
import MathlibExt.AlgebraicTopology.Spectra.Sequential.MappingTelescope.IntegerStablePiHo
import MathlibExt.AlgebraicTopology.Spectra.Sequential.StableHomotopy.IntegerColimitNormalization

/-!
# The original Q cofiber maps on all integer homotopy functors

The original whole-arrow Q, native I cone and chosen cofiber define the
actual target inclusion. Its level-homotopy image retains the inverse Q
counit and the chosen inclusion. Every integer group map uses the original
filtered quotient functor on those same maps. Complete Arrow naturality
preserves both original components and the counit's inverse.

The long exact sequence and fiber-to-loop-cofiber comparison require the
separate sphere-representative and suspension kernel arguments.
-/

set_option autoImplicit false
noncomputable section
universe u v
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open scoped CGWH.modelCategory

namespace PointedCGWH.SequentialSpectrum.StableHomotopy.CofiberIntegerSequence

open HomotopicalAlgebra.EnrichedProjective.Native
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK.NativeK
open PointedCGWH.SequentialSpectrum.MappingTelescope.IntegerStablePiGeometry
open PointedCGWH.SequentialSpectrum.MappingTelescope.IntegerStablePiHoGeometry

attribute [local instance] CategoryTheory.SequentialSpectrum.EnrichedIndex.enrichedCategory
  HomotopicalAlgebra.EnrichedProjective.Native.modelCategory
  PointedCGWH.EnrichedMapping.hasSmallLimits
  MonoidalClosed.enrichedCategorySelf HomotopicalAlgebra.EnrichedProjective.Native.allObjectsFibrant

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
private abbrev Index := PointedCGWH.Spectra.Sequential.Index.{u, v}
private abbrev H := toHomotopyCategory PointedCGWH.SequentialSpectrum.{u, v}
private abbrev Q := Replacement.cofibrantReplacement (B := B) (A := Index)
private abbrev ε := Replacement.cofibrantReplacementCounit (B := B) (A := Index)

/-- The same original chosen Q cofiber is kept on every complete source arrow. -/
abbrev cofiber : Arrow PointedCGWH.SequentialSpectrum.{u, v} ⥤ PointedCGWH.SequentialSpectrum :=
  CofiberNullity.cofiberQ (B := B)

/-- The actual target inclusion of the original chosen whole-arrow Q cofiber. -/
def inclusion (F : Arrow PointedCGWH.SequentialSpectrum.{u, v}) :
    Q.obj F.right ⟶ cofiber.obj F :=
  (OriginalISuspension.cocone (B := B) (Q.mapArrow.obj F)).inr

/-- The full target inclusion is natural on the original two-component arrow square. -/
theorem inclusion_naturality {F G : Arrow PointedCGWH.SequentialSpectrum.{u, v}}
    (q : F ⟶ G) :
    Q.map q.right ≫ inclusion G = inclusion F ≫ cofiber.map q := by
  exact (OrdinaryHoChosenPuppe.cofiberMap_target
    (OriginalICone.cone (B := B)) (OriginalICone.inclusion (B := B))
    (OriginalISuspension.cocone (B := B))
    (OriginalISuspension.coconeIsColimit (B := B)) (Q.mapArrow.map q)).symm

/-- The original level-weak Q counit has its actual image isomorphism. -/
def qCounitHoIso (X : PointedCGWH.SequentialSpectrum.{u, v}) : H.obj (Q.obj X) ≅ H.obj X :=
  Localization.Construction.wIso (ε.app X)
    (Replacement.cofibrantReplacementCounit_mem_trivialFibrations (B := B) X).2

/-- The source target-to-cofiber arrow keeps the original Q inverse and actual chosen inclusion. -/
def inclusionHo (F : Arrow PointedCGWH.SequentialSpectrum.{u, v}) :
    H.obj F.right ⟶ H.obj (cofiber.obj F) :=
  (qCounitHoIso F.right).inv ≫ H.map (inclusion F)

/-- Every integer degree retains the exact original Q/inclusion group map. -/
def inclusionInteger (q : ℤ) (F : Arrow PointedCGWH.SequentialSpectrum.{u, v}) :
    (integerStablePiHoFunctor q).obj (H.obj F.right) ⟶
      (integerStablePiHoFunctor q).obj (H.obj (cofiber.obj F)) :=
  (integerStablePiHoFunctor q).map (inclusionHo F)

/-- The full cofiber group map is the original quotient map of the Q comparison and inclusion. -/
theorem inclusionInteger_formula (q : ℤ) (F : Arrow PointedCGWH.SequentialSpectrum.{u, v}) :
    inclusionInteger q F =
      (integerStablePiHoFunctor q).map (qCounitHoIso F.right).inv ≫
        (integerStablePiFunctor q).map (inclusion F) := by
  rw [inclusionInteger, inclusionHo, Functor.map_comp, integerStablePiHoFunctor_map]
  rfl

/-- The unchanged counit retains its whole original input-map square. -/
theorem qCounitHoIso_naturality {X Y : PointedCGWH.SequentialSpectrum.{u, v}} (f : X ⟶ Y) :
    H.map (Q.map f) ≫ (qCounitHoIso Y).hom = (qCounitHoIso X).hom ≫ H.map f :=
  (H.map_comp _ _).symm.trans ((H.congr_map (ε.naturality f)).trans (H.map_comp _ _))

/-- Both full inverse counit functions retain the original input map. -/
theorem qCounitHoIso_inverse_naturality {X Y : PointedCGWH.SequentialSpectrum.{u, v}}
    (f : X ⟶ Y) :
    H.map f ≫ (qCounitHoIso Y).inv = (qCounitHoIso X).inv ≫ H.map (Q.map f) := by
  apply (cancel_epi (qCounitHoIso X).hom).mp
  calc
    (qCounitHoIso X).hom ≫ (H.map f ≫ (qCounitHoIso Y).inv) =
        H.map (Q.map f) ≫ ((qCounitHoIso Y).hom ≫ (qCounitHoIso Y).inv) := by
      rw [← Category.assoc, ← qCounitHoIso_naturality f, Category.assoc]
    _ = H.map (Q.map f) := by rw [Iso.hom_inv_id, Category.comp_id]
    _ = (qCounitHoIso X).hom ≫ ((qCounitHoIso X).inv ≫ H.map (Q.map f)) := by
      rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp]

/-- The original whole-arrow target function acts naturally on the actual cofiber inclusion. -/
theorem inclusionHo_naturality {F G : Arrow PointedCGWH.SequentialSpectrum.{u, v}}
    (m : F ⟶ G) :
    H.map m.right ≫ inclusionHo G = inclusionHo F ≫ H.map (cofiber.map m) := by
  rw [inclusionHo, inclusionHo, ← Category.assoc, qCounitHoIso_inverse_naturality,
    Category.assoc, ← H.map_comp, inclusion_naturality,
    H.map_comp, ← Category.assoc]

/-- Every integer quotient map retains both full original Arrow target maps. -/
theorem inclusionInteger_naturality (q : ℤ)
    {F G : Arrow PointedCGWH.SequentialSpectrum.{u, v}} (m : F ⟶ G) :
    (integerStablePiFunctor q).map m.right ≫ inclusionInteger q G =
      inclusionInteger q F ≫ (integerStablePiFunctor q).map (cofiber.map m) := by
  have h := (integerStablePiHoFunctor q).congr_map (inclusionHo_naturality m)
  simp only [Functor.map_comp, integerStablePiHoFunctor_map] at h
  exact h

/-- The original Q cofiber boundary retains its actual chosen suspension target. -/
def boundary (F : Arrow PointedCGWH.SequentialSpectrum.{u, v}) :
    cofiber.obj F ⟶ (OriginalISuspension.suspension (B := B)).obj (Q.obj F.left) :=
  OrdinaryHoChosenPuppe.boundary
    (OriginalICone.cone (B := B)) (OriginalICone.inclusion (B := B))
    (OriginalISuspension.cocone (B := B)) (OriginalISuspension.coconeIsColimit (B := B))
    Diagrams.zeroDiagram Diagrams.zeroDiagram_isZero (Q.mapArrow.obj F)

/-- Every entire Q arrow retains the original cofiber-boundary square. -/
theorem boundary_naturality {F G : Arrow PointedCGWH.SequentialSpectrum.{u, v}}
    (m : F ⟶ G) :
    cofiber.map m ≫ boundary G = boundary F ≫
      (OriginalISuspension.suspension (B := B)).map (Q.map m.left) :=
  OrdinaryHoChosenPuppe.boundary_naturality
    (OriginalICone.cone (B := B)) (OriginalICone.inclusion (B := B))
    (OriginalISuspension.cocone (B := B)) (OriginalISuspension.coconeIsColimit (B := B))
    Diagrams.zeroDiagram Diagrams.zeroDiagram_isZero (Q.mapArrow.map m)

/-- The boundary's full cone leg is the unchanged original suspension cone leg. -/
theorem boundary_cone (F : Arrow PointedCGWH.SequentialSpectrum.{u, v}) :
    (OriginalISuspension.cocone (B := B) (Q.mapArrow.obj F)).inl ≫ boundary F =
      (OriginalISuspension.cocone (B := B)
        (Arrow.mk (Diagrams.toZero (Q.obj F.left)))).inl :=
  OrdinaryHoChosenPuppe.boundary_cone
    (OriginalICone.cone (B := B)) (OriginalICone.inclusion (B := B))
    (OriginalISuspension.cocone (B := B)) (OriginalISuspension.coconeIsColimit (B := B))
    Diagrams.zeroDiagram Diagrams.zeroDiagram_isZero (Q.mapArrow.obj F)

/-- The complete target leg of the boundary factors through the original native zero. -/
theorem inclusion_boundary (F : Arrow PointedCGWH.SequentialSpectrum.{u, v}) :
    inclusion F ≫ boundary F = Diagrams.toZero (Q.obj F.right) ≫
      (OriginalISuspension.cocone (B := B)
        (Arrow.mk (Diagrams.toZero (Q.obj F.left)))).inr :=
  OrdinaryHoChosenPuppe.boundary_target
    (OriginalICone.cone (B := B)) (OriginalICone.inclusion (B := B))
    (OriginalISuspension.cocone (B := B)) (OriginalISuspension.coconeIsColimit (B := B))
    Diagrams.zeroDiagram Diagrams.zeroDiagram_isZero (Q.mapArrow.obj F)

end PointedCGWH.SequentialSpectrum.StableHomotopy.CofiberIntegerSequence
