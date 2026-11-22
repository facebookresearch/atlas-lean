/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.Spectra.Sequential.Stabilization
public import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Sequential.StabilizationFamily

/-!
# Adjunct formulas for sequential stabilization maps

In a braided monoidal closed category with an initial object, the free/evaluation
adjunct of a sequential stabilization map is expressed using the inverse braiding and
the successor Hom comparison. At the tensor-unit coefficient, this specializes to the
successor comparison followed by the inverse left unitor.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
universe u v
open CategoryTheory Limits MonoidalCategory BraidedCategory
open scoped MonoidalClosed

namespace CategoryTheory.Spectra.Sequential

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [BraidedCategory C] [MonoidalClosed C] [HasInitial C]
attribute [local instance] CategoryTheory.SequentialSpectrum.EnrichedIndex.enrichedCategory

private theorem free_unit_action (K : C) (n : ℕ) (A : C) (b : Index K) :
    ((freeAtEvaluationAdjunction K n).unit.app A ▷
      CategoryTheory.SequentialSpectrum.EnrichedIndex.indexHom K
        (CategoryTheory.SequentialSpectrum.EnrichedIndex.degree K n) b) ≫
      EnrichedFunctorCat.Free.action
        (CategoryTheory.SequentialSpectrum.EnrichedIndex.degree K n) A
        (CategoryTheory.SequentialSpectrum.EnrichedIndex.degree K n) b =
      𝟙 (A ⊗ CategoryTheory.SequentialSpectrum.EnrichedIndex.indexHom K
        (CategoryTheory.SequentialSpectrum.EnrichedIndex.degree K n) b) := by
  let a := CategoryTheory.SequentialSpectrum.EnrichedIndex.degree K n
  let F := (freeAt K n).obj A
  let H := CategoryTheory.SequentialSpectrum.EnrichedIndex.indexHom K a b
  let U := CategoryTheory.SequentialSpectrum.EnrichedIndex.indexHom K a a
  let u : A ⟶ A ⊗ U := (freeAtEvaluationAdjunction K n).unit.app A
  have hu : EnrichedFunctorCat.Free.evaluate a A F (𝟙 F) = u := by
    have h := (freeAtEvaluationAdjunction K n).homEquiv_id A
    change (EnrichedFunctorCat.Free.adjunction a).homEquiv A F (𝟙 F) = u at h
    rw [EnrichedFunctorCat.Free.adjunction_homEquiv] at h
    exact h
  have h := EnrichedFunctorCat.Free.reconstruct_component a A F (𝟙 F) b
  rw [EnrichedFunctorCat.component_id, hu] at h
  change 𝟙 (A ⊗ H) = (u ⊗ₘ 𝟙 H) ≫
    MonoidalClosed.uncurry (F.toEnrichedFunctor.map a b) at h
  have hAction :
      (MonoidalClosed.uncurry (F.toEnrichedFunctor.map a b) : (A ⊗ U) ⊗ H ⟶ A ⊗ H) =
        EnrichedFunctorCat.Free.action a A a b :=
    EnrichedFunctorCat.Free.object_uncurry_map a a b A
  have hPost := congrArg (fun q : (A ⊗ U) ⊗ H ⟶ A ⊗ H => (u ▷ H) ≫ q) hAction
  have hTensor := congrArg
    (fun q : A ⊗ H ⟶ (A ⊗ U) ⊗ H => q ≫ MonoidalClosed.uncurry (F.toEnrichedFunctor.map a b))
    (tensorHom_id u H)
  exact (h.trans (hTensor.trans hPost)).symm

/-- The actual stabilization adjunct is the inverse positive braid followed
by the literal inverse of the successor Hom comparison. -/
theorem stabilizationMap_homEquiv_normalized (K : C) (n : ℕ) (A : C) :
    (freeAtEvaluationAdjunction K (n + 1)).homEquiv (K ⊗ A) ((freeAt K n).obj A)
        (stabilizationMap K n A) =
      (β_ A K).inv ≫
        (A ◁ (CategoryTheory.SequentialSpectrum.EnrichedIndex.indexHomSuccessorIso K n).inv) := by
  let a := CategoryTheory.SequentialSpectrum.EnrichedIndex.degree K n
  let b := CategoryTheory.SequentialSpectrum.EnrichedIndex.degree K (n + 1)
  let U := CategoryTheory.SequentialSpectrum.EnrichedIndex.indexHom K a a
  let H := CategoryTheory.SequentialSpectrum.EnrichedIndex.indexHom K a b
  let F := (freeAt K n).obj A
  let u : A ⟶ A ⊗ U := (freeAtEvaluationAdjunction K n).unit.app A
  let e : H ≅ K := CategoryTheory.SequentialSpectrum.EnrichedIndex.indexHomSuccessorIso K n
  let act : (A ⊗ U) ⊗ H ⟶ A ⊗ H := EnrichedFunctorCat.Free.action a A a b
  have hUnit : (u ▷ H) ≫ act = 𝟙 (A ⊗ H) := free_unit_action K n A b
  have hPrefix : (K ◁ u) ≫ (e.inv ▷ (A ⊗ U)) = (e.inv ▷ A) ≫ (H ◁ u) :=
    whisker_exchange e.inv u
  have hBraid : (H ◁ u) ≫ (β_ (A ⊗ U) H).inv = (β_ A H).inv ≫ (u ▷ H) :=
    braiding_inv_naturality_right H u
  have hMove : (e.inv ▷ A) ≫ (β_ A H).inv = (β_ A K).inv ≫ (A ◁ e.inv) :=
    braiding_inv_naturality_left e.inv A
  have hStructure : structureMap F n =
      (e.inv ▷ (A ⊗ U)) ≫ (β_ (A ⊗ U) H).inv ≫ act := by
    change (e.inv ⊗ₘ 𝟙 (A ⊗ U)) ≫ (β_ (A ⊗ U) H).inv ≫
      MonoidalClosed.uncurry (F.toEnrichedFunctor.map a b) = _
    rw [tensorHom_id, EnrichedFunctorCat.Free.object_uncurry_map]
  rw [stabilizationMap_homEquiv]
  change (K ◁ u) ≫ structureMap F n = (β_ A K).inv ≫ (A ◁ e.inv)
  rw [hStructure]
  rw [reassoc_of% hPrefix, reassoc_of% hBraid, hUnit, Category.comp_id]
  exact hMove


end CategoryTheory.Spectra.Sequential

namespace PointedCGWH.SequentialSpectrum

attribute [local instance] CategoryTheory.SequentialSpectrum.EnrichedIndex.enrichedCategory

/-- The actual unit stabilization adjunct is the inverse successor Hom map
followed by the actual left unitor inverse on that complete Hom object. -/
theorem unitStabilizationMap_homEquiv_normalized (K : PointedCGWH.{u, v}) (n : ℕ) :
    (freeAtEvaluationAdjunction K (n + 1)).homEquiv
        K ((freeAt K n).obj (𝟙_ PointedCGWH.{u, v})) (unitStabilizationMap K n) =
      (CategoryTheory.SequentialSpectrum.EnrichedIndex.indexHomSuccessorIso K n).inv ≫
        (λ_ (CategoryTheory.SequentialSpectrum.EnrichedIndex.indexHom K
          (CategoryTheory.SequentialSpectrum.EnrichedIndex.degree K n)
          (CategoryTheory.SequentialSpectrum.EnrichedIndex.degree K (n + 1)))).inv := by
  let H := CategoryTheory.SequentialSpectrum.EnrichedIndex.indexHom K
    (CategoryTheory.SequentialSpectrum.EnrichedIndex.degree K n)
    (CategoryTheory.SequentialSpectrum.EnrichedIndex.degree K (n + 1))
  let e : H ≅ K := CategoryTheory.SequentialSpectrum.EnrichedIndex.indexHomSuccessorIso K n
  let F := (CategoryTheory.Spectra.Sequential.freeAt K n).obj (𝟙_ PointedCGWH.{u, v})
  let u : (𝟙_ PointedCGWH.{u, v}) ⟶ CategoryTheory.Spectra.Sequential.level F n :=
    (CategoryTheory.Spectra.Sequential.freeAtEvaluationAdjunction K n).unit.app
      (𝟙_ PointedCGWH.{u, v})
  let s : K ⊗ CategoryTheory.Spectra.Sequential.level F n ⟶ (𝟙_ PointedCGWH.{u, v}) ⊗ H :=
    CategoryTheory.Spectra.Sequential.structureMap F n
  have hNorm : (K ◁ u) ≫ s = (β_ (𝟙_ PointedCGWH.{u, v}) K).inv ≫
      (𝟙_ PointedCGWH.{u, v} ◁ e.inv) := by
    have h := CategoryTheory.Spectra.Sequential.stabilizationMap_homEquiv_normalized K n
      (𝟙_ PointedCGWH.{u, v})
    rw [CategoryTheory.Spectra.Sequential.stabilizationMap_homEquiv] at h
    exact h
  have hFormula : (freeAtEvaluationAdjunction K (n + 1)).homEquiv
      K ((freeAt K n).obj (𝟙_ PointedCGWH.{u, v})) (unitStabilizationMap K n) =
      (ρ_ K).inv ≫ (K ◁ u) ≫ s := unitStabilizationMap_homEquiv K n
  have hPre := congrArg (fun q : K ⊗ (𝟙_ PointedCGWH.{u, v}) ⟶
    (𝟙_ PointedCGWH.{u, v}) ⊗ H => (ρ_ K).inv ≫ q) hNorm
  have hUnitors : (ρ_ K).inv ≫ (β_ (𝟙_ PointedCGWH.{u, v}) K).inv ≫
      (𝟙_ PointedCGWH.{u, v} ◁ e.inv) = e.inv ≫ (λ_ H).inv := by
    rw [braiding_inv_tensorUnit_left]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    exact (leftUnitor_inv_naturality e.inv).symm
  exact hFormula.trans (hPre.trans hUnitors)


end PointedCGWH.SequentialSpectrum
