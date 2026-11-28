/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Author: @toskua -/

module

public import MathlibExt.Algebra.Homology.FirstQuadrantFirstPageMappingConeNaturality
public import MathlibExt.LinearAlgebra.Filtration.Exactness
public import MathlibExt.CategoryTheory.NatTrans.PointwiseImage
public import MathlibExtTest.Algebra.Homology.FirstQuadrantFiltrationHomotopyBoundary
public import Mathlib.Data.ZMod.Basic

/-!
# Coherent first-page maps and finite exactness descent

Tripling the integer doubling bicomplex gives actual nonidentity maps of coherent windows,
cokernels, mapping cones and first-page comparisons. A nested image diagram has doubling
at each object and coefficient tripling along its inner transition.

The separate finite-descent client uses ZMod 6 with stage one equal to the whole module and
all other stages zero. This family is exhaustive but not monotone. Its actual identity/zero
quotient maps are exact, so the general finite-descent API applies without strengthening
its hypotheses to a monotone filtration or a field of coefficients.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ComposableArrows HomologicalComplex₂
open MathlibExtTest.Algebra.Homology.FirstQuadrantFirstPageFocusedClients
open MathlibExtTest.Algebra.Homology.FirstQuadrantFiltrationHomotopyBoundary

namespace MathlibExtTest.Algebra.Homology.FirstQuadrantCoherentNaturalityClients

example : ((triple.f 1).f 0).hom (1 : ℤ) = (3 : ℤ) := rfl

example : (((triple ≫ triple).f 1).f 0).hom (1 : ℤ) = (9 : ℤ) := rfl

example : horizontalFirstPageCoherentMap K 0 = horizontalFirstPageFiltrationMap K 0 :=
  horizontalFirstPageCoherentMap_zero K

example : horizontalFirstPageCoherentMap K 1 = horizontalFirstPageNextFiltrationMap K 0 :=
  horizontalFirstPageCoherentMap_succ K 0

example : horizontalFirstPageCoherentMap K 1 ≫
    horizontalFirstPageCoherentUpperCochainMapOfBicomplex triple 1 =
      horizontalFirstPageCoherentLowerCochainMapOfBicomplex triple 1 ≫
        horizontalFirstPageCoherentMap K 1 :=
  horizontalFirstPageCoherentMap_naturality_of_bicomplex triple 1

example : cokernel.π (horizontalFirstPageCoherentMap K 1) ≫
    horizontalFirstPageCoherentCokernelMapOfBicomplex triple 1 =
      horizontalFirstPageCoherentUpperCochainMapOfBicomplex triple 1 ≫
        cokernel.π (horizontalFirstPageCoherentMap K 1) :=
  horizontalFirstPageCoherentCokernelMapOfBicomplex_π triple 1

example : horizontalFirstPageCoherentCokernelMapOfBicomplex triple 1 ≫
    (horizontalFirstPageCoherentCokernelIso K 1).hom =
      (horizontalFirstPageCoherentCokernelIso K 1).hom ≫
        horizontalDirectColumnCochainMap triple 1 :=
  horizontalFirstPageCoherentCokernelIso_hom_naturality_of_bicomplex triple 1

example : (horizontalFirstPageCoherentCokernelShortComplexMapOfBicomplex triple 1).τ₁ =
    horizontalFirstPageCoherentLowerCochainMapOfBicomplex triple 1 :=
  horizontalFirstPageCoherentCokernelShortComplexMapOfBicomplex_τ₁ triple 1

example : (horizontalFirstPageCoherentCokernelShortComplexMapOfBicomplex triple 1).τ₂ =
    horizontalFirstPageCoherentUpperCochainMapOfBicomplex triple 1 :=
  horizontalFirstPageCoherentCokernelShortComplexMapOfBicomplex_τ₂ triple 1

example : (horizontalFirstPageCoherentCokernelShortComplexMapOfBicomplex triple 1).τ₃ =
    horizontalFirstPageCoherentCokernelMapOfBicomplex triple 1 :=
  horizontalFirstPageCoherentCokernelShortComplexMapOfBicomplex_τ₃ triple 1

example : (horizontalCompleteFiltrationMappingConeNatTrans triple).app
    (mk₁ (homOfLE (horizontalFirstPageCoherentIndex_le 1))) ≫
      horizontalFirstPageCoherentMappingConeToDirectColumn K 1 =
        horizontalFirstPageCoherentMappingConeToDirectColumn K 1 ≫
          horizontalDirectColumnCochainMap triple 1 :=
  horizontalFirstPageCoherentMappingConeToDirectColumn_naturality_of_bicomplex triple 1

example : QuasiIso (horizontalFirstPageCoherentMappingConeToDirectColumn K 1) :=
  horizontalFirstPageCoherentMappingConeToDirectColumn_quasiIso K 1

example : (horizontalFirstPageCoherentAdjacentShortComplexIso K 0).hom.τ₃ =
    (horizontalFirstPageCoherentAdjacentShortComplexIso K 1).hom.τ₁ :=
  horizontalFirstPageCoherentAdjacentShortComplexIso_endpoint_coherence K 0

example : horizontalFirstPageCoherentConnectingMap K 0 0 =
    horizontalFirstPageAdjacentConnectingMap K 0 0 :=
  horizontalFirstPageCoherentConnectingMap_eq_adjacent K 0 0

example : ((horizontalFirstQuadrantSpectralSequence K).page 1).d (1, 0) (0, 0) ≫
    (horizontalFirstPageCoherentVerticalHomologyIso K 0 0).hom =
      (horizontalFirstPageCoherentVerticalHomologyIso K 1 0).hom ≫
        (((0 + 1 : ℕ) : ℤ).negOnePow • horizontalFirstPageHorizontalHomologyMap K 0 0) :=
  horizontalFirstPage_d_coherentVerticalHomology_eq_horizontal K 0 0

/-- A genuine inner coefficient transition on the integer module. -/
def innerDiagram : Fin 2 ⥤ ModuleCat ℤ := mk₁ (𝟙 Z + 𝟙 Z + 𝟙 Z)

/-- Repeat the coefficient transition in an independent outer index. -/
def imageDiagram : Fin 2 ⥤ Fin 2 ⥤ ModuleCat ℤ :=
  (Functor.const (Fin 2)).obj innerDiagram

/-- Doubling at every object, naturally with the tripling transition. -/
def doubling : imageDiagram ⟶ imageDiagram := 𝟙 imageDiagram + 𝟙 imageDiagram

example : ((doubling.app (0 : Fin 2)).app (0 : Fin 2)).hom (1 : ℤ) = (2 : ℤ) := rfl

example : ((NatTrans.pointwiseImage doubling).obj (0 : Fin 2)).obj (0 : Fin 2) =
    image ((doubling.app (0 : Fin 2)).app (0 : Fin 2)) :=
  NatTrans.pointwiseImage_obj_obj doubling 0 0

example : ((NatTrans.pointwiseImage doubling).obj (0 : Fin 2)).map
    (homOfLE (show (0 : Fin 2) ≤ 1 by decide)) =
      image.map (Arrow.homMk
        ((imageDiagram.obj (0 : Fin 2)).map (homOfLE (show (0 : Fin 2) ≤ 1 by decide)))
        ((imageDiagram.obj (0 : Fin 2)).map (homOfLE (show (0 : Fin 2) ≤ 1 by decide)))
        ((doubling.app (0 : Fin 2)).naturality
          (homOfLE (show (0 : Fin 2) ≤ 1 by decide)))) :=
  NatTrans.pointwiseImage_obj_map doubling 0 (homOfLE (show (0 : Fin 2) ≤ 1 by decide))

/-- A coefficient module with nonzero integral torsion. -/
abbrev Torsion := ZMod 6

/-- An exhaustive family whose top stage is followed by a zero stage. -/
def stages (p : ℕ) : Submodule ℤ Torsion := if p = 1 then ⊤ else ⊥

lemma preserves_id (p : ℕ) (x : Torsion) (hx : x ∈ stages p) :
    (LinearMap.id : Torsion →ₗ[ℤ] Torsion) x ∈ stages p := hx

lemma preserves_zero (p : ℕ) (x : Torsion) (_hx : x ∈ stages p) :
    (0 : Torsion →ₗ[ℤ] Torsion) x ∈ stages p := (stages p).zero_mem

lemma layer_id (p : ℕ) :
    (LinearMap.id : Torsion →ₗ[ℤ] Torsion).filtrationLayerMap
      stages stages preserves_id p = LinearMap.id := by
  apply LinearMap.ext
  intro q
  refine Quotient.inductionOn q ?_
  intro x
  rfl

lemma layer_zero (p : ℕ) :
    (0 : Torsion →ₗ[ℤ] Torsion).filtrationLayerMap
      stages stages preserves_zero p = 0 := by
  apply LinearMap.ext
  intro q
  refine Quotient.inductionOn q ?_
  intro x
  rfl

example : ¬ Monotone stages := by
  intro h
  have h12 := h (show (1 : ℕ) ≤ 2 by decide)
  have h1 : (1 : Torsion) ∈ stages 1 := by simp [stages]
  have h2 := h12 h1
  have hz : (1 : Torsion) = 0 := by simpa [stages] using h2
  exact (show (1 : ZMod 6) ≠ 0 by decide) hz

example : LinearMap.range (LinearMap.id : Torsion →ₗ[ℤ] Torsion) =
    LinearMap.ker (0 : Torsion →ₗ[ℤ] Torsion) := by
  apply LinearMap.range_eq_ker_of_exact_filtrationLayers
    (LinearMap.id : Torsion →ₗ[ℤ] Torsion) (0 : Torsion →ₗ[ℤ] Torsion)
    stages stages stages preserves_id preserves_zero
  · ext x
    rfl
  · simp [stages]
  · intro x
    exact ⟨1, by simp [stages]⟩
  · intro p
    rw [layer_id, layer_zero]
    simp

end MathlibExtTest.Algebra.Homology.FirstQuadrantCoherentNaturalityClients
