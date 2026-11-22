/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.CategoryTheory.Enriched.LeftKanTensor
import MathlibExt.CategoryTheory.Enriched.RightKanExtension
import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.BasedHomotopyExtension
import MathlibExt.Topology.Category.PointedCGWH.SmallKanCoends
import MathlibExt.Topology.Category.PointedCGWH.EnrichedMappingEnds

/-!
# The original native index adjunctions preserve homotopy extension

The complete original tensor comparison for enriched Kan extension
retains its actual unit and both inverse maps. Its unit-coefficient
characteristic and scalar naturality prove the literal free-time endpoint
square. The actual Hom adjunction transports arbitrary target homotopies
to the source and transfers both extension equations through this square.

The complete restriction commutes with the same scalar time action at
every original object. Its actual right Kan Hom adjunction transfers both
equations of the original extension to each arbitrary native target.
All original homotopies, source maps and target objects are retained.
-/

set_option autoImplicit false
noncomputable section
universe u v

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open CategoryTheory.EnrichedFunctorCat
open PointedCGWH.EnrichedIntervalContraction
open scoped MonoidalClosed CGWH.modelCategory

namespace HomotopicalAlgebra.EnrichedProjective.Native.NativeIndexKanHomotopyExtension

variable {A D : Type} [EnrichedCategory PointedCGWH.{u, v} A]
  [EnrichedCategory PointedCGWH.{u, v} D]

attribute [local instance] PointedCGWH.EnrichedMapping.hasSmallLimits
  MonoidalClosed.enrichedCategorySelf MonoidalClosed.enrichedOrdinaryCategorySelf
  PointedCGWH.EnrichedKan.hasObjectCoproduct PointedCGWH.EnrichedKan.hasRelationCoproduct
  PointedCGWH.EnrichedKan.hasBalancingCoequalizer

/-- The complete original Kan tensor comparison carries the actual scalar
inverse unitor to the actual scalar inverse unitor of the full Kan object. -/
theorem leftKan_scalarUnit_inverse
    (j : EnrichedFunctor PointedCGWH.{u, v} A D)
    (X : EnrichedFunctorCat PointedCGWH.{u, v} A) :
    (leftKan j).map (scalarUnitIso X).inv ≫
        leftKanTensorHom j (𝟙_ PointedCGWH.{u, v}) X =
      (scalarUnitIso ((leftKan j).obj X)).inv := by
  apply (leftKanHomEquiv j X (tensorLeftObject (𝟙_ PointedCGWH.{u, v}) ((leftKan j).obj X))).injective
  rw [leftKanHomEquiv_naturality_left]
  apply hom_ext
  intro a
  rw [component_comp,
    leftKanHomEquiv_apply, leftKanHomToRestriction_component,
    leftKanHomEquiv_apply, leftKanHomToRestriction_component]
  let U := X.toEnrichedFunctor.obj a
  let Z := ((leftKan j).obj X).toEnrichedFunctor.obj (j.obj a)
  have hA : (component (scalarUnitIso X).inv a : U ⟶ (𝟙_ PointedCGWH.{u, v}) ⊗ U) =
      (λ_ U).inv := scalarUnitIso_inv_component X a
  have hTensor :
      (leftKanUnitComponent j (tensorLeftObject (𝟙_ PointedCGWH.{u, v}) X) a ≫
        component (leftKanTensorHom j (𝟙_ PointedCGWH.{u, v}) X) (j.obj a) :
        ((𝟙_ PointedCGWH.{u, v}) ⊗ U) ⟶ ((𝟙_ PointedCGWH.{u, v}) ⊗ Z)) =
      (𝟙_ PointedCGWH.{u, v}) ◁ leftKanUnitComponent j X a :=
    leftKanTensorHom_unit j (𝟙_ PointedCGWH.{u, v}) X a
  have hB : (component (scalarUnitIso ((leftKan j).obj X)).inv (j.obj a) :
      Z ⟶ ((𝟙_ PointedCGWH.{u, v}) ⊗ Z)) = (λ_ Z).inv :=
    scalarUnitIso_inv_component ((leftKan j).obj X) (j.obj a)
  have hLeft := congrArg₂
    (fun (f : U ⟶ ((𝟙_ PointedCGWH.{u, v}) ⊗ U))
      (g : ((𝟙_ PointedCGWH.{u, v}) ⊗ U) ⟶ ((𝟙_ PointedCGWH.{u, v}) ⊗ Z)) => f ≫ g)
    hA hTensor
  have hRight := congrArg (fun g : Z ⟶ ((𝟙_ PointedCGWH.{u, v}) ⊗ Z) =>
    leftKanUnitComponent j X a ≫ g) hB
  exact hLeft.trans ((leftUnitor_inv_naturality (leftKanUnitComponent j X a)).symm.trans hRight.symm)

/-- Every literal original time endpoint commutes with the whole Kan
tensor comparison, including the original inverse scalar unitor. -/
theorem leftKan_timeInclusion
    (j : EnrichedFunctor PointedCGWH.{u, v} A D)
    (t : unitInterval) (X : EnrichedFunctorCat PointedCGWH.{u, v} A) :
    (leftKan j).map (timeInclusion t X) ≫
        leftKanTensorHom j PointedCGWH.RealizedIntervalContraction.time X =
      timeInclusion t ((leftKan j).obj X) := by
  rw [timeInclusion, timeInclusion, Functor.map_comp, Category.assoc,
    leftKanTensorHom_scalar_naturality, ← Category.assoc, leftKan_scalarUnit_inverse]

/-- The genuine original enriched Kan extension preserves all-target
native homotopy extension on every original source arrow. -/
theorem leftKan_map_HEP
    (j : EnrichedFunctor PointedCGWH.{u, v} A D)
    {X Y : EnrichedFunctorCat PointedCGWH.{u, v} A} (i : X ⟶ Y)
    (hi : PointedCGWH.EnrichedBasedHomotopyExtension.property i) :
    PointedCGWH.EnrichedBasedHomotopyExtension.property ((leftKan j).map i) := by
  exact IntervalHomotopyExtension.map_mem_of_adjunction (leftKanRestrictionAdjunction j)
    timeFunctor (timeInclusionNatTrans 0) timeFunctor (timeInclusionNatTrans 0)
    (leftKanTensorNatIso j PointedCGWH.RealizedIntervalContraction.time)
    (fun X => leftKan_timeInclusion j 0 X) i hi

/-- The whole original restriction preserves all-target native homotopy
extension through its original scalar time and complete target action. -/
theorem restriction_map_HEP
    (j : EnrichedFunctor PointedCGWH.{u, v} A D)
    {X Y : EnrichedFunctorCat PointedCGWH.{u, v} D} (i : X ⟶ Y)
    (hi : PointedCGWH.EnrichedBasedHomotopyExtension.property i) :
    PointedCGWH.EnrichedBasedHomotopyExtension.property ((restriction j).map i) := by
  let eForward : restriction j ⋙ timeFunctor ≅ timeFunctor ⋙ restriction j :=
    NatIso.ofComponents
      (fun X => tensorLeftRestrictionIso PointedCGWH.RealizedIntervalContraction.time j X)
      (by
        intro X Y f
        exact tensorLeftRestrictionIso_naturality PointedCGWH.RealizedIntervalContraction.time j f)
  let e := eForward.symm
  apply IntervalHomotopyExtension.map_mem_of_adjunction (rightKanAdjunction j)
    timeFunctor (timeInclusionNatTrans 0) timeFunctor (timeInclusionNatTrans 0) e ?_ i hi
  intro X
  apply hom_ext
  intro a
  change component ((restriction j).map (timeInclusion 0 X) ≫
      (tensorLeftRestrictionIso PointedCGWH.RealizedIntervalContraction.time j X).inv) a =
    component (timeInclusion 0 ((restriction j).obj X)) a
  let U := X.toEnrichedFunctor.obj (j.obj a)
  let T := PointedCGWH.RealizedIntervalContraction.time.{u, v}
  have hMap : (component ((restriction j).map (timeInclusion 0 X)) a : U ⟶ T ⊗ U) =
      (λ_ U).inv ≫ PointedCGWH.freePointIntervalEndpoint.{u, v} 0 ▷ U :=
    (restrictionMap_component j (timeInclusion 0 X) a).trans (timeInclusion_component 0 X (j.obj a))
  have hIso : (component (tensorLeftRestrictionIso T j X).inv a : T ⊗ U ⟶ T ⊗ U) =
      𝟙 (T ⊗ U) := tensorLeftRestrictionIso_inv_component T j X a
  have hSource := component_comp ((restriction j).map (timeInclusion 0 X))
    (tensorLeftRestrictionIso T j X).inv a
  have hLeft := congrArg₂ (fun (f : U ⟶ T ⊗ U) (g : T ⊗ U ⟶ T ⊗ U) => f ≫ g) hMap hIso
  have hTarget := timeInclusion_component 0 ((restriction j).obj X) a
  exact hSource.trans (hLeft.trans ((Category.comp_id _).trans hTarget.symm))

/-- The full original prolongation followed by the full original
restriction preserves every original homotopy-extension arrow. -/
theorem up_map_HEP
    (j : EnrichedFunctor PointedCGWH.{u, v} A D)
    {X Y : EnrichedFunctorCat PointedCGWH.{u, v} A} (i : X ⟶ Y)
    (hi : PointedCGWH.EnrichedBasedHomotopyExtension.property i) :
    PointedCGWH.EnrichedBasedHomotopyExtension.property ((leftKan j ⋙ restriction j).map i) :=
  restriction_map_HEP j ((leftKan j).map i) (leftKan_map_HEP j i hi)

end HomotopicalAlgebra.EnrichedProjective.Native.NativeIndexKanHomotopyExtension
