/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Authors: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.RootChangeColimits
public import MathlibExtTest.CategoryTheory.SmallObject.GoodCellTreeBoundedLowerPresentation
public import MathlibExtTest.CategoryTheory.SmallObject.GoodCellTreeRelativePresentability

/-!
# Original root-change colimits and the fixed-rank counterexample

The actual constant Nat-to-PUnit arrow gives the same native root-change
functor. It is aleph0-accessible but maps the initial under-PUnit object
to the original infinite-fold endpoint, which is not aleph0-presentable
under Nat. The original empty-tree colimit and all native comparison
functions retain their actual choices and independent attaching labels.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 512

noncomputable section

universe t

open CategoryTheory CategoryTheory.Limits CategoryTheory.SmallObject
  BoundedLowerSupport RootChangeColimits

namespace RootChangeColimitExamples

attribute [local instance] Cardinal.fact_isRegular_aleph0

/-- The actual original constant root from the complete adjacent-fold example. -/
abbrev originalRoot : ℕ ⟶ PUnit.{1} := BoundedLowerPresentationExamples.root

/-- The original empty target tree retains the actual PUnit identity root and family. -/
def unitTree : CellTree GoodCellTreeDataExamples.foldFamily PUnit.{1}
    (P := GoodCellTreeDataExamples.NoVertices) :=
  CellTree.empty GoodCellTreeDataExamples.foldFamily PUnit.{1}

theorem unitTree_original_root : unitTree.{t}.hom = 𝟙 PUnit.{1} := rfl

theorem unitTree_good : unitTree.{t}.IsGood Cardinal.aleph0.{0} :=
  CellTree.emptyIsGood Cardinal.aleph0.{0}

/-- Its actual initial endpoint is presentable under the same PUnit root. -/
theorem originalInitialPresentable :
    IsCardinalPresentable unitTree.{t}.endpointObj Cardinal.aleph0.{0} :=
  RelativeCellPresentability.endpoint Cardinal.aleph0.{0}
    unitTree.{t} unitTree_good.{t}
    (hasCardinalLT_of_finite GoodCellTreeDataExamples.NoVertices Cardinal.aleph0.{0} le_rfl)

/-- The same native functor is accessible at precisely the original aleph0 rank. -/
theorem originalRootAccessible :
    (Under.map originalRoot).IsCardinalAccessible Cardinal.aleph0.{0} := inferInstance

/-- The root change is genuinely nonmonomorphic on its actual Nat source. -/
theorem originalRootNotMono : ¬ Mono originalRoot := by
  intro h
  have he : (0 : ℕ) = 1 := (mono_iff_injective originalRoot).1 h rfl
  exact Nat.zero_ne_one he

/-- Keep the actual identity-on-right comparison to the original infinite-fold endpoint. -/
def originalMappedInitialIso :
    (Under.map originalRoot).obj unitTree.{t}.endpointObj ≅
      BoundedLowerPresentationExamples.tree.{t}.endpointObj :=
  Under.isoMk (Iso.refl PUnit.{1}) (by
    change (originalRoot ≫ 𝟙 PUnit.{1}) ≫ 𝟙 PUnit.{1} = originalRoot
    simp only [Category.comp_id])

theorem originalMappedInitialIso_hom_right :
    originalMappedInitialIso.{t}.hom.right = 𝟙 PUnit.{1} := rfl

theorem originalMappedInitialIso_inv_right :
    originalMappedInitialIso.{t}.inv.right = 𝟙 PUnit.{1} := rfl

theorem originalMappedInitialIso_root :
    (originalRoot ≫ unitTree.{t}.hom) ≫ originalMappedInitialIso.{t}.hom.right =
      BoundedLowerPresentationExamples.tree.{t}.hom :=
  Under.w originalMappedInitialIso.{t}.hom

/-- The original image of the presentable initial object is NOT presentable at the same rank. -/
theorem originalMappedInitialNotPresentable :
    ¬ IsCardinalPresentable ((Under.map originalRoot).obj unitTree.{t}.endpointObj)
      Cardinal.aleph0.{0} := by
  intro h
  let : IsCardinalPresentable ((Under.map originalRoot).obj unitTree.{t}.endpointObj)
      Cardinal.aleph0.{0} := h
  exact BoundedLowerPresentationExamples.endpoint_not_presentable.{t}
    (isCardinalPresentable_of_iso originalMappedInitialIso.{t} Cardinal.aleph0.{0})

/-- This actual native functor distinguishes accessibility from fixed-rank object compactness. -/
theorem originalAccessibleRankCounterexample :
    (Under.map originalRoot).IsCardinalAccessible Cardinal.aleph0.{0} ∧
      IsCardinalPresentable unitTree.{t}.endpointObj Cardinal.aleph0.{0} ∧
        ¬ IsCardinalPresentable ((Under.map originalRoot).obj unitTree.{t}.endpointObj)
          Cardinal.aleph0.{0} :=
  ⟨originalRootAccessible, originalInitialPresentable.{t},
    originalMappedInitialNotPresentable.{t}⟩

/-- The original bounded support carrier of this empty tree still has its actual connectedness. -/
instance originalSupportsConnected :
    IsConnected (Carrier (P := GoodCellTreeDataExamples.NoVertices) Cardinal.aleph0.{0}) :=
  IsFiltered.isConnected _

/-- The exact original native presentation, before root change. -/
def originalUnitPresentation :
    ColimitPresentation (Carrier (P := GoodCellTreeDataExamples.NoVertices) Cardinal.aleph0.{0})
      unitTree.{t}.endpointObj :=
  BoundedLowerPresentation.treePresentation Cardinal.aleph0.{0}
    unitTree.{t} unitTree_good.{t} unitTree.{t}.lowerData

/-- Map that SAME original presentation by the actual original Nat root arrow. -/
def originalMappedUnitPresentation :
    ColimitPresentation (Carrier (P := GoodCellTreeDataExamples.NoVertices) Cardinal.aleph0.{0})
      ((Under.map originalRoot).obj unitTree.{t}.endpointObj) :=
  mappedPresentation originalRoot originalUnitPresentation.{t}

theorem originalMappedUnitPresentation_diag :
    originalMappedUnitPresentation.{t}.diag =
      originalUnitPresentation.{t}.diag ⋙ Under.map originalRoot := rfl

/-- Both original forgetful functors genuinely create this chosen connected shape's colimits. -/
def originalConnectedCreation :
    CreatesColimitsOfShape
        (Carrier (P := GoodCellTreeDataExamples.NoVertices) Cardinal.aleph0.{0})
        (Under.forget ℕ) ×
      CreatesColimitsOfShape
        (Carrier (P := GoodCellTreeDataExamples.NoVertices) Cardinal.aleph0.{0})
        (Under.forget PUnit.{1}) :=
  ⟨Under.createsColimitsOfShapeForgetOfIsConnected,
    Under.createsColimitsOfShapeForgetOfIsConnected⟩

/-- Reflection applies to precisely the same native mapped cocone. -/
theorem originalUnitColimitReflected :
    Nonempty (IsColimit originalUnitPresentation.{t}.cocone) := by
  exact (mappedCocone_isColimit_iff originalRoot originalUnitPresentation.{t}.cocone).1
    ⟨isColimitOfPreserves (Under.map originalRoot) originalUnitPresentation.{t}.isColimit⟩

/-- Every original native leg-right function survives mapping. -/
theorem originalMappedLegFunctions :
    (fun B : Carrier (P := GoodCellTreeDataExamples.NoVertices) Cardinal.aleph0.{0} =>
      (originalMappedUnitPresentation.{t}.ι.app B).right) =
      (fun B : Carrier (P := GoodCellTreeDataExamples.NoVertices) Cardinal.aleph0.{0} =>
        (originalUnitPresentation.{t}.ι.app B).right) :=
  mappedPresentation_leg_right_function originalRoot originalUnitPresentation.{t}

/-- The complete original unmapped leg function uses exactly the original lower maps and Iso. -/
theorem originalUnitLegFunctions :
    (fun B : Carrier (P := GoodCellTreeDataExamples.NoVertices) Cardinal.aleph0.{0} =>
      originalUnitPresentation.{t}.ι.app B) =
      (fun B : Carrier (P := GoodCellTreeDataExamples.NoVertices) Cardinal.aleph0.{0} =>
        unitTree.{t}.lowerData.map (le_top : B.1 ≤ ⊤) ≫
          (unitTree.{t}.endpointIso unitTree.{t}.lowerData).hom) :=
  BoundedLowerPresentation.treePresentation_leg_function Cardinal.aleph0.{0}
    unitTree.{t} unitTree_good.{t} unitTree.{t}.lowerData

/-- A second original root arrow, with its actual displayed value in Fin 2. -/
def secondRoot : PUnit.{1} ⟶ Fin 2 := ↾fun _ => 0

/-- The exact native composition comparison at the original identity under Fin 2. -/
def originalCompositionIso :
    (Under.map (originalRoot ≫ secondRoot)).obj (Under.mk (𝟙 (Fin 2))) ≅
      (Under.map originalRoot).obj ((Under.map secondRoot).obj (Under.mk (𝟙 (Fin 2)))) :=
  (Under.mapComp originalRoot secondRoot).app (Under.mk (𝟙 (Fin 2)))

theorem originalCompositionIso_hom_right :
    originalCompositionIso.hom.right = 𝟙 (Fin 2) :=
  compositionIso_hom_right originalRoot secondRoot (Under.mk (𝟙 (Fin 2)))

theorem originalCompositionIso_inv_right :
    originalCompositionIso.inv.right = 𝟙 (Fin 2) :=
  compositionIso_inv_right originalRoot secondRoot (Under.mk (𝟙 (Fin 2)))

theorem originalCompositionRoot :
    ((Under.map (originalRoot ≫ secondRoot)).obj (Under.mk (𝟙 (Fin 2)))).hom =
      ((Under.map originalRoot).obj ((Under.map secondRoot).obj (Under.mk (𝟙 (Fin 2))))).hom :=
  congrFun (composition_root_function originalRoot secondRoot) (Under.mk (𝟙 (Fin 2)))

/-- Original identity coherence has the exact right identity in both directions. -/
theorem originalIdentityComparison :
    ((Under.mapId ℕ).hom.app GoodCellTreeDataExamples.quotientTree.{t}.endpointObj).right =
        𝟙 GoodCellTreeDataExamples.quotientTree.{t}.endpointObj.right ∧
      ((Under.mapId ℕ).inv.app GoodCellTreeDataExamples.quotientTree.{t}.endpointObj).right =
        𝟙 GoodCellTreeDataExamples.quotientTree.{t}.endpointObj.right :=
  ⟨Under.mapId_hom_app_right _ _, Under.mapId_inv_app_right _ _⟩

end RootChangeColimitExamples
