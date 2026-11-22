/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.StabilizationK
import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNativeKan
import MathlibExt.AlgebraicTopology.ModelCategory.QuillenBrown
import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.CofibrantFree
import Mathlib.CategoryTheory.Adjunction.Limits

/-!
# Full native coefficient-unit propagation for both component index adjunctions

Every source and target native index category is retained. The complete
coend adjunction is the actual level Quillen adjunction, and pointwise
restriction carries all original level weak maps. Naturality transfers all
source Omega Hom tests before an index or coefficient arrow is selected.
-/

set_option autoImplicit false
noncomputable section
universe u v
open CategoryTheory CategoryTheory.Limits CategoryTheory.EnrichedFunctorCat
open HomotopicalAlgebra
open scoped CGWH.limits CGWH.modelCategory MonoidalClosed

namespace HomotopicalAlgebra.EnrichedProjective.Native.IndexUnitWeakCoefficientPropagation
open OperatorStabilizationK
attribute [local instance] HomotopicalAlgebra.EnrichedProjective.Native.modelCategory
  PointedCGWH.EnrichedMapping.hasSmallLimits MonoidalClosed.enrichedCategorySelf
variable {A D L : Type} [EnrichedCategory PointedCGWH.{u, v} A]
  [EnrichedCategory PointedCGWH.{u, v} D]
  [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]

/-- The complete original level coend and pointwise restriction preserve every weak cofibrant source arrow for every
native target index category. -/
theorem up_map_levelWeak (j : EnrichedFunctor PointedCGWH.{u, v} A D)
    {X Y : EnrichedFunctorCat PointedCGWH.{u, v} A} [IsCofibrant X] [IsCofibrant Y]
    (f : X ⟶ Y) (hf : weakEquivalences (EnrichedFunctorCat PointedCGWH.{u, v} A) f) :
    weakEquivalences (EnrichedFunctorCat PointedCGWH.{u, v} A)
      ((EnrichedFunctorCat.leftKan j ⋙ EnrichedFunctorCat.restriction j).map f) := by
  let _ : (EnrichedFunctorCat.leftKanRestrictionAdjunction j).IsQuillenAdjunction := by
    have h := HomotopicalAlgebra.EnrichedProjective.Native.Kan.leftKanRestriction_isQuillen j
    change @Adjunction.IsQuillenAdjunction _ _ _ _
      (Construction.modelCategory (A := A)) (Construction.modelCategory (A := D)) _ _ _ at h
    rw [Construction.modelCategory_eq_native (A := A) (B := B),
      Construction.modelCategory_eq_native (A := D) (B := B)] at h
    exact h
  let _ : WeakEquivalence f := (HomotopicalAlgebra.weakEquivalence_iff _).mpr hf
  have hP : WeakEquivalence ((EnrichedFunctorCat.leftKan j).map f) :=
    Adjunction.IsQuillenAdjunction.map_weakEquivalence_of_cofibrant
      (adj := EnrichedFunctorCat.leftKanRestrictionAdjunction j) f
  have hLevelP : weakEquivalences (EnrichedFunctorCat PointedCGWH.{u, v} D)
      ((EnrichedFunctorCat.leftKan j).map f) := (HomotopicalAlgebra.weakEquivalence_iff _).mp hP
  rw [HomotopicalAlgebra.EnrichedProjective.Native.weakEquivalences_eq,
    EvaluationTransfer.evaluationProperty_iff] at hLevelP ⊢
  intro a
  change weakEquivalences PointedCGWH.{u, v}
    (component (EnrichedFunctorCat.restrictionMap j ((EnrichedFunctorCat.leftKan j).map f)) a)
  rw [EnrichedFunctorCat.restrictionMap_component]
  exact hLevelP (j.obj a)

/-- Every Omega-target source Hom test of the entire actual Kan unit transfers in both directions along cofibrant weak
arrows. -/
theorem unit_omegaTests_iff_of_levelWeak (s : NativeStabilizationFamily.{u, v} A L)
    (j : EnrichedFunctor PointedCGWH.{u, v} A D)
    {X Y : EnrichedFunctorCat PointedCGWH.{u, v} A} [IsCofibrant X] [IsCofibrant Y]
    (f : X ⟶ Y) (hf : weakEquivalences (EnrichedFunctorCat PointedCGWH.{u, v} A) f) :
    NativeK.omegaTests s ((EnrichedFunctorCat.leftKanRestrictionAdjunction j).unit.app X) ↔
      NativeK.omegaTests s ((EnrichedFunctorCat.leftKanRestrictionAdjunction j).unit.app Y) := by
  have hF : NativeK.omegaTests s f := NativeK.levelWeak_le_omegaTests s f hf
  have hUP : NativeK.omegaTests s ((EnrichedFunctorCat.leftKan j ⋙ EnrichedFunctorCat.restriction j).map f) :=
    NativeK.levelWeak_le_omegaTests s _ (up_map_levelWeak j f hf)
  have hNat : (EnrichedFunctorCat.leftKanRestrictionAdjunction j).unit.app X ≫
      (EnrichedFunctorCat.leftKan j ⋙ EnrichedFunctorCat.restriction j).map f =
      f ≫ (EnrichedFunctorCat.leftKanRestrictionAdjunction j).unit.app Y :=
    ((EnrichedFunctorCat.leftKanRestrictionAdjunction j).unit.naturality f).symm
  calc
    NativeK.omegaTests s ((EnrichedFunctorCat.leftKanRestrictionAdjunction j).unit.app X) ↔
        NativeK.omegaTests s ((EnrichedFunctorCat.leftKanRestrictionAdjunction j).unit.app X ≫
          (EnrichedFunctorCat.leftKan j ⋙ EnrichedFunctorCat.restriction j).map f) :=
      ((NativeK.omegaTests s).postcomp_iff _ _ hUP).symm
    _ ↔ NativeK.omegaTests s (f ≫ (EnrichedFunctorCat.leftKanRestrictionAdjunction j).unit.app Y) := by
      rw [hNat]
    _ ↔ NativeK.omegaTests s ((EnrichedFunctorCat.leftKanRestrictionAdjunction j).unit.app Y) :=
      (NativeK.omegaTests s).precomp_iff _ _ hF

/-- The entire free-coefficient unit test equivalence retains every original index and weak cofibrant coefficient,
including the actual sequential--symmetric component. -/
theorem freeUnit_omegaTests_iff_of_coefficientWeak (s : NativeStabilizationFamily.{u, v} A L)
    (j : EnrichedFunctor PointedCGWH.{u, v} A D) (a : A)
    {T T' : PointedCGWH.{u, v}} [IsCofibrant T] [IsCofibrant T']
    (h : T ⟶ T') (hh : weakEquivalences PointedCGWH.{u, v} h) :
    NativeK.omegaTests s ((EnrichedFunctorCat.leftKanRestrictionAdjunction j).unit.app (Free.object a T)) ↔
      NativeK.omegaTests s ((EnrichedFunctorCat.leftKanRestrictionAdjunction j).unit.app (Free.object a T')) := by
  let _ : IsCofibrant (Free.object (V := PointedCGWH.{u, v}) a T) :=
    NativeK.freeCoefficient_cofibrant a T
  let _ : IsCofibrant (Free.object (V := PointedCGWH.{u, v}) a T') :=
    NativeK.freeCoefficient_cofibrant a T'
  let _ : (Free.adjunction (V := PointedCGWH.{u, v}) a).IsQuillenAdjunction :=
    freeAtEvaluation_isQuillenAdjunction a
  let _ : WeakEquivalence h := (HomotopicalAlgebra.weakEquivalence_iff _).mpr hh
  have hFree : WeakEquivalence ((Free.functor (V := PointedCGWH.{u, v}) a).map h) :=
    Adjunction.IsQuillenAdjunction.map_weakEquivalence_of_cofibrant (adj := Free.adjunction a) h
  exact unit_omegaTests_iff_of_levelWeak s j ((Free.functor a).map h)
    ((HomotopicalAlgebra.weakEquivalence_iff _).mp hFree)

omit B in
/-- The genuine Kan unit at every initial source is an isomorphism. Both Kan adjunctions supply the required
preservation of the same initial object. -/
theorem unit_isIso_of_isInitial (j : EnrichedFunctor PointedCGWH.{u, v} A D)
    (X : EnrichedFunctorCat PointedCGWH.{u, v} A) (hX : IsInitial X) :
    IsIso ((EnrichedFunctorCat.leftKanRestrictionAdjunction j).unit.app X) := by
  let _ : PreservesColimits (EnrichedFunctorCat.leftKan j) :=
    (EnrichedFunctorCat.leftKanRestrictionAdjunction j).leftAdjoint_preservesColimits
  let _ : PreservesColimits (EnrichedFunctorCat.restriction j) :=
    (EnrichedFunctorCat.rightKanAdjunction j).leftAdjoint_preservesColimits
  exact isIso_of_isInitial hX
    (hX.isInitialObj (EnrichedFunctorCat.leftKan j ⋙ EnrichedFunctorCat.restriction j)) _

/-- Every initial source has all Omega tests of its actual Kan unit for every stabilization family. -/
theorem unit_omegaTests_of_isInitial (s : NativeStabilizationFamily.{u, v} A L)
    (j : EnrichedFunctor PointedCGWH.{u, v} A D)
    (X : EnrichedFunctorCat PointedCGWH.{u, v} A) (hX : IsInitial X) :
    NativeK.omegaTests s ((EnrichedFunctorCat.leftKanRestrictionAdjunction j).unit.app X) := by
  let _ : IsIso ((EnrichedFunctorCat.leftKanRestrictionAdjunction j).unit.app X) :=
    unit_isIso_of_isInitial j X hX
  exact (NativeK.omegaTests s).of_isIso _

/-- A cofibrant source weakly equivalent to an actual initial source has all Kan-unit Omega tests.
Cofibrancy of the initial target is derived from its genuine universal property. -/
theorem unit_omegaTests_of_levelWeak_to_initial (s : NativeStabilizationFamily.{u, v} A L)
    (j : EnrichedFunctor PointedCGWH.{u, v} A D)
    {X Y : EnrichedFunctorCat PointedCGWH.{u, v} A} [IsCofibrant X]
    (hY : IsInitial Y) (f : X ⟶ Y)
    (hf : weakEquivalences (EnrichedFunctorCat PointedCGWH.{u, v} A) f) :
    NativeK.omegaTests s ((EnrichedFunctorCat.leftKanRestrictionAdjunction j).unit.app X) := by
  let _ : IsCofibrant Y := (isCofibrant_iff_of_isInitial (𝟙 Y) hY).mpr inferInstance
  exact (unit_omegaTests_iff_of_levelWeak s j f hf).mpr (unit_omegaTests_of_isInitial s j Y hY)

/-- Every free cofibrant coefficient weakly equivalent to an actual initial coefficient has all Kan-unit
Omega tests at every source index. The initial coefficient and its full free object remain explicit. -/
theorem freeUnit_omegaTests_of_coefficientWeak_to_initial (s : NativeStabilizationFamily.{u, v} A L)
    (j : EnrichedFunctor PointedCGWH.{u, v} A D) (a : A)
    {T T' : PointedCGWH.{u, v}} [IsCofibrant T]
    (hT' : IsInitial T') (h : T ⟶ T') (hh : weakEquivalences PointedCGWH.{u, v} h) :
    NativeK.omegaTests s ((EnrichedFunctorCat.leftKanRestrictionAdjunction j).unit.app (Free.object a T)) := by
  let _ : IsCofibrant T' := (isCofibrant_iff_of_isInitial (𝟙 T') hT').mpr inferInstance
  let _ : PreservesColimits (Free.functor (V := PointedCGWH.{u, v}) a) :=
    (Free.adjunction (V := PointedCGWH.{u, v}) a).leftAdjoint_preservesColimits
  have hFree : IsInitial (Free.object (V := PointedCGWH.{u, v}) a T') :=
    hT'.isInitialObj (Free.functor a)
  exact (freeUnit_omegaTests_iff_of_coefficientWeak s j a h hh).mpr
    (unit_omegaTests_of_isInitial s j (Free.object a T') hFree)

end HomotopicalAlgebra.EnrichedProjective.Native.IndexUnitWeakCoefficientPropagation
