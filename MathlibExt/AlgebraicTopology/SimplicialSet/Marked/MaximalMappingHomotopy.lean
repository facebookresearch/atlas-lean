/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.MaximalMappingComposition
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.MappingZeroUnit
import Mathlib.AlgebraicTopology.SimplicialSet.Homotopy
import MathlibExt.AlgebraicTopology.SimplicialSet.MonoidalCompat

/-!
# Actual maximal marked parameter homotopies act on whole mapping spaces

A supplied marked interval-parameter family acts by the original full
mapping composition. Its original endpoint equations give a genuine
simplicial homotopy between the same original source-precomposition maps.
The interval need not be Kan and no marked-model structure is assumed.
-/

noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory
open scoped Simplicial

namespace SSet.Marked

/-- Composition with the original constant marked mapping vertex is exactly original source precomposition. -/
theorem maxMappingComposition_zero (P Y : Marked.{u}) (f : P ⟶ P) :
    (mappingComplex .maximal P Y ◁ maxCurry ((zeroParameterUnitIso .maximal P).hom ≫ f)) ≫
        maxMappingComposition P P Y =
      (SSet.stdSimplex.rightUnitor (mappingComplex .maximal P Y)).hom ≫ mappingComplexPre .maximal f Y := by
  ext n g
  apply Hom.ext
  rfl

private theorem rightUnitor_inv_endpoint (M : SSet.{u}) (ε : Fin 2) :
    (SSet.stdSimplex.rightUnitor M).inv ≫ (M ◁ SSet.stdSimplex.δ ε) =
      if ε = 1 then SSet.ι₀ else SSet.ι₁ := by
  fin_cases ε
  · exact SSet.stdSimplex.rightUnitor_inv_map_δ_zero M
  · exact SSet.stdSimplex.rightUnitor_inv_map_δ_one M

/-- The whole original maximal marked interval family gives the native source-precomposition homotopy with
  its same endpoints. -/
def maximalMappingPreHomotopy {P : Marked.{u}} (Y : Marked.{u}) (f₀ f₁ : P ⟶ P)
    (H : prod (max (Δ[1] : SSet.{u})) P ⟶ P)
    (h₀ : prodMap (maximal.map (SSet.stdSimplex.δ (1 : Fin 2))) (𝟙 P) ≫ H =
      (zeroParameterUnitIso .maximal P).hom ≫ f₀)
    (h₁ : prodMap (maximal.map (SSet.stdSimplex.δ (0 : Fin 2))) (𝟙 P) ≫ H =
      (zeroParameterUnitIso .maximal P).hom ≫ f₁) :
    SSet.Homotopy (mappingComplexPre .maximal f₀ Y) (mappingComplexPre .maximal f₁ Y) := by
  let M := mappingComplex .maximal P Y
  let h : M ⊗ (Δ[1] : SSet.{u}) ⟶ M := (M ◁ maxCurry H) ≫ maxMappingComposition P P Y
  have hface (ε : Fin 2) (f : P ⟶ P)
      (hf : prodMap (maximal.map (SSet.stdSimplex.δ ε)) (𝟙 P) ≫ H =
        (zeroParameterUnitIso .maximal P).hom ≫ f) :
      ((SSet.stdSimplex.rightUnitor M).inv ≫ (M ◁ SSet.stdSimplex.δ ε)) ≫ h =
        mappingComplexPre .maximal f Y := by
    have hc : SSet.stdSimplex.δ ε ≫ maxCurry H = maxCurry ((zeroParameterUnitIso .maximal P).hom ≫ f) :=
      (maxCurry_pre _ H).symm.trans (congrArg maxCurry hf)
    let U : M ⟶ M ⊗ (Δ[0] : SSet.{u}) := (SSet.stdSimplex.rightUnitor M).inv
    let A : M ⊗ (Δ[0] : SSet.{u}) ⟶ M ⊗ (Δ[1] : SSet.{u}) := M ◁ SSet.stdSimplex.δ ε
    let B : M ⊗ (Δ[1] : SSet.{u}) ⟶ M ⊗ mappingComplex .maximal P P := M ◁ maxCurry H
    let C : M ⊗ mappingComplex .maximal P P ⟶ M := maxMappingComposition P P Y
    let R : M ⊗ (Δ[0] : SSet.{u}) ⟶ M ⊗ mappingComplex .maximal P P :=
      M ◁ maxCurry ((zeroParameterUnitIso .maximal P).hom ≫ f)
    have hAB : A ≫ B = R :=
      (MonoidalCategory.whiskerLeft_comp M (SSet.stdSimplex.δ ε) (maxCurry H)).symm.trans
        (congrArg (fun q => M ◁ q) hc)
    have hRC : R ≫ C = (SSet.stdSimplex.rightUnitor M).hom ≫ mappingComplexPre .maximal f Y :=
      maxMappingComposition_zero P Y f
    change (U ≫ A) ≫ (B ≫ C) = _
    calc
      _ = U ≫ ((A ≫ B) ≫ C) := (Category.assoc _ _ _).trans
        (congrArg (fun q => U ≫ q) (Category.assoc A B C).symm)
      _ = U ≫ (R ≫ C) := congrArg (fun q => U ≫ (q ≫ C)) hAB
      _ = U ≫ ((SSet.stdSimplex.rightUnitor M).hom ≫ mappingComplexPre .maximal f Y) :=
        congrArg (fun q => U ≫ q) hRC
      _ = _ := (SSet.stdSimplex.rightUnitor M).inv_hom_id_assoc _
  exact
    { h := h
      h₀ := (congrArg (fun q => q ≫ h) (rightUnitor_inv_endpoint M 1).symm).trans (hface 1 f₀ h₀)
      h₁ := (congrArg (fun q => q ≫ h) (rightUnitor_inv_endpoint M 0).symm).trans (hface 0 f₁ h₁)
      rel := by ext n ⟨⟨x, hx⟩, t⟩; cases hx }

end SSet.Marked
