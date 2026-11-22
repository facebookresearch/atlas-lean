/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.ScalarTensorEnrichment
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoefficientTensor
import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono

/-!
# Whole enriched tensors by original arbitrary marked parameters

The original marked parameter, including its exact selected mark set,
is kept unchanged as the first coordinate. Whole maximal Hom prisms
act only on the original coefficient. This constructs the missing
arbitrary marked-parameter enriched tensor and specializes exactly to
the proved maximal scalar tensor. Cofibration preservation is the
original marked-mono law; no weak-compatibility law for arbitrary marks
is assumed or asserted.
-/

noncomputable section
universe u v
open CategoryTheory MonoidalCategory Opposite HomotopicalAlgebra
open scoped Simplicial

namespace SSet.Marked
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory coefficientMarkedModelCategory

/-- An arbitrary original marked parameter stays unchanged in every entire enriched Hom prism. -/
def markedTensorMapping (A X Y : Marked.{u}) :
    mappingComplex .maximal X Y ⟶ mappingComplex .maximal (prod A X) (prod A Y) where
  app n := ↾fun f =>
    prodLift
      (prodSnd (max (SSet.stdSimplex.obj n.unop)) (prod A X) ≫ prodFst A X)
      (prodLift (prodFst (max (SSet.stdSimplex.obj n.unop)) (prod A X))
        (prodSnd (max (SSet.stdSimplex.obj n.unop)) (prod A X) ≫ prodSnd A X) ≫ f)
  naturality n m a := by
    ext f
    apply Hom.ext
    rfl

/-- The genuine original marked parameter tensor is enriched, preserving whole native Hom identity and composition. -/
def markedTensorEnriched (A : Marked.{u}) : EnrichedFunctor SSet.{u} Marked.{u} Marked.{u} where
  obj X := prod A X
  map := markedTensorMapping A
  map_id X := by ext n z; apply Hom.ext; rfl
  map_comp X Y Z := by ext n fg; apply Hom.ext; rfl

/-- Whole marked tensoring acts on original marked enriched diagrams and their full natural maps. -/
def enrichedDiagramMarkedTensor (C : Type v) [EnrichedCategory SSet.{u} C] (A : Marked.{u}) :
    EnrichedDiagram C ⥤ EnrichedDiagram C where
  obj F := F.comp SSet.{u} (markedTensorEnriched A)
  map {F G} α :=
    { app x := prodMap (𝟙 A) (α.app x)
      naturality x y := by
        ext n f
        apply Hom.ext
        ext q z
        have h := congr($(α.naturality x y).app n f)
        have h' := congrArg (fun a => a.hom.app q (z.1, z.2.2)) h
        exact Prod.ext rfl h' }
  map_id F := by
    apply EnrichedDiagramMap.ext
    funext x
    exact prodMap_id A (F.obj x)
  map_comp α β := by
    apply EnrichedDiagramMap.ext
    funext x
    exact (prodMap_comp (𝟙 A) (𝟙 A) (α.app x) (β.app x)).symm

/-- Maximal parameters recover the existing scalar Hom tensor with exactly the same full marked map. -/
theorem markedTensorMapping_max (K : SSet.{u}) (X Y : Marked.{u}) :
    markedTensorMapping (max K) X Y = scalarTensorMapping K X Y := rfl

/-- The whole original maximal scalar diagram tensor is exactly the specialization of the arbitrary marked tensor. -/
theorem enrichedDiagramMarkedTensor_max (C : Type v) [EnrichedCategory SSet.{u} C] (K : SSet.{u}) :
    enrichedDiagramMarkedTensor C (max K) = enrichedDiagramTensor C K := rfl

/-- Original marked parameter and coefficient coordinates survive every scalar simplex readback. -/
theorem markedTensorMapping_app (A X Y : Marked.{u}) (n : ℕ)
    (f : (mappingComplex .maximal X Y) _⦋n⦌) (q : SimplexCategoryᵒᵖ)
    (z : (SSet.stdSimplex.obj ⦋n⦌ ⊗ (A.toSSet ⊗ X.toSSet)).obj q) :
    ((markedTensorMapping A X Y).app (op ⦋n⦌) f).hom.app q z =
      (z.2.1, f.hom.app q (z.1, z.2.2)) := rfl

/-- Product with any original marked parameter preserves marked monos, without discarding or enlarging its mark set. -/
theorem markedTensorMap_mono (A : Marked.{u}) {X Y : Marked.{u}} (f : X ⟶ Y) [Mono f] :
    Mono (prodMap (𝟙 A) f) := by
  let _ : forget.IsRightAdjoint := minimalAdjunction.isRightAdjoint
  let hUnderlying : Mono f.hom := inferInstanceAs (Mono (forget.map f))
  let _ : Mono f.hom := hUnderlying
  apply forget.mono_of_mono_map
  change Mono ((𝟙 A.toSSet) ⊗ₘ f.hom)
  let _ : ∀ q : SimplexCategoryᵒᵖ, Mono (((𝟙 A.toSSet) ⊗ₘ f.hom).app q) := fun q => by
    apply (mono_iff_injective _).mpr
    intro z z' h
    let _ : Mono (f.hom.app q) := (NatTrans.mono_iff_mono_app f.hom).mp hUnderlying q
    change (z.1, f.hom.app q z.2) = (z'.1, f.hom.app q z'.2) at h
    exact Prod.ext (congrArg (fun y : (A.toSSet ⊗ Y.toSSet).obj q => y.1) h)
      (injective_of_mono (f.hom.app q)
        (congrArg (fun y : (A.toSSet ⊗ Y.toSSet).obj q => y.2) h))
  exact NatTrans.mono_of_mono_app _

/-- The actual coefficient cofibration class is preserved by the exact arbitrary marked tensor; weak
  compatibility remains a separate statement. -/
theorem markedTensor_preserves_cofibrations (A : Marked.{u}) {X Y : Marked.{u}} (f : X ⟶ Y)
    (hf : cofibrations Marked.{u} f) : cofibrations Marked.{u} (prodMap (𝟙 A) f) := by
  rw [coefficientMarkedCofibrations_eq] at hf ⊢
  let _ : Mono f := hf
  exact markedTensorMap_mono A f

end SSet.Marked
