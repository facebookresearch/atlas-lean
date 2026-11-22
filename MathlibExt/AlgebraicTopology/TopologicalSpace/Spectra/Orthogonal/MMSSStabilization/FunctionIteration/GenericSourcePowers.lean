/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.CategoryTheory.Functor.CoaugmentationIteration
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.NativeOrthogonalFreePairBifunctor
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Orthogonal.CanonicalSourceSmashClosed
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Orthogonal.CanonicalSourceSmashUnit
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Orthogonal.CanonicalSourceFreeSmash
import MathlibExt.CategoryTheory.Monoidal.Closed.InternalHomInterchange
import MathlibExt.CategoryTheory.Monoidal.Closed.InternalCurryingSourceNaturality
import MathlibExt.CategoryTheory.Monoidal.RightModuleFreeCoefficient
import MathlibExt.CategoryTheory.Monoidal.Closed.UnitEvaluation

/-!
# Generic full free-source power data used by native FunctionIteration

The arbitrary-category and selected-source power data retain their original
native maps. Both generic source-currying naturality laws are supplied by
the canonical closed monoidal API. FunctionIteration imports this module.
-/

set_option autoImplicit false
noncomputable section
universe u v

open CategoryTheory MonoidalCategory BraidedCategory Limits
open CategoryTheory.Enriched CategoryTheory.EnrichedFunctorCat CategoryTheory.Spectra
open CategoryTheory.Spectra.OrthogonalSourceRightModule
open scoped MonoidalClosed

section CurrentFullFreeSourceBindings


set_option autoImplicit false
noncomputable section
open CategoryTheory MonoidalCategory Limits
open CategoryTheory.EnrichedFunctorCat
open PointedCGWH.Spectra.Orthogonal
open PointedCGWH.Spectra.NativeStableMonoidal
open scoped CategoryTheory.MonObj MonoidalClosed

namespace PointedCGWH.Spectra.Orthogonal.MMSSStabilization.FunctionIteration.IndependentFullFreeSuccessor
universe uC vC uD vD
variable {C : Type uC} [Category.{vC} C] [MonoidalCategory C]
  {D : Type uD} [Category.{vD} D]

/-- The full original component type binds the entire native tensor and both complete coefficient functors. -/
abbrev ComponentType (native : MonoidalCategory D) (F : ℕ → C ⥤ D) (S : ℕ → C) (n : ℕ) : Type _ :=
  letI := native
  (F 1).obj (S 1) ⊗ (F n).obj (S n) ≅ (F (n + 1)).obj (S (n + 1))

end PointedCGWH.Spectra.Orthogonal.MMSSStabilization.FunctionIteration.IndependentFullFreeSuccessor

namespace PointedCGWH.Spectra.Orthogonal.MMSSStabilization.FunctionIteration.TypedFullPowerData
universe uV vV uJ
attribute [local instance] Enriched.prodCategory MonoidalLeftAction.monoidalOppositeLeftAction
attribute [local instance] EnrichedDayKernel.ColimitMonoidal.smallestColimits
variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [SymmetricCategory V] [MonoidalClosed V]
  [Category ℕ] [MonoidalCategory ℕ] [SymmetricCategory ℕ]
  [EnrichedOrdinaryCategory V ℕ] [HasColimitsOfSize.{0, 0} V]
  [HasProducts.{0} V] [HasEqualizers V]
  {q : Enriched.ModuleMappingR.SelectedSource V ℕ}
  {J : Type uJ} [EnrichedCategory V J]
  (c : CanonicalSourceFreeSmash.SelectedPair.Context q J)

/-- The whole original source/E context chooses both the actual tensor and actual closed functor. -/
abbrev sourceContext : CanonicalSourceSmash.SourceContext q (EnrichedFunctorCat V J) :=
  { equivalence := c.sourceEquivalence }

/-- Every free-family value retains its entire actual native free coefficient functor. -/
abbrev object (S : ℕ → V) (n : ℕ) : EnrichedFunctorCat V J :=
  (Free.functor (c.indexMap n)).obj (S n)

end PointedCGWH.Spectra.Orthogonal.MMSSStabilization.FunctionIteration.TypedFullPowerData

namespace PointedCGWH.Spectra.Orthogonal.MMSSStabilization.FunctionIteration.OriginalSelectedPowerData
universe uV vV uJ
attribute [local instance] Enriched.prodCategory MonoidalLeftAction.monoidalOppositeLeftAction
attribute [local instance] EnrichedDayKernel.ColimitMonoidal.smallestColimits
variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [SymmetricCategory V] [MonoidalClosed V]
  [Category ℕ] [MonoidalCategory ℕ] [SymmetricCategory ℕ]
  [EnrichedOrdinaryCategory V ℕ] [HasColimitsOfSize.{0, 0} V]
  [HasProducts.{0} V] [HasEqualizers V]
  {q : Enriched.ModuleMappingR.SelectedSource V ℕ}
  {J : Type uJ} [EnrichedCategory V J]
  (c : CanonicalSourceFreeSmash.SelectedPair.Context q J)

/-- The entire original selected relative tensor, transported through both complete source functors. -/
def monoidalData : MonoidalCategory (EnrichedFunctorCat V J) :=
  (TypedFullPowerData.sourceContext c).monoidalCategory

/-- The complete original selected Mapping_R closed data at that same transported tensor. -/
def closedData : letI := monoidalData c; MonoidalClosed (EnrichedFunctorCat V J) :=
  CanonicalSourceSmashClosed.Selected.monoidalClosed (TypedFullPowerData.sourceContext c)

/-- The complete chosen tensor is the original source transport, with its full source category. -/
theorem monoidalData_original : monoidalData c =
    ({ equivalence := c.sourceEquivalence } :
      CanonicalSourceSmash.SourceContext q (EnrichedFunctorCat V J)).monoidalCategory := rfl

/-- The complete chosen closed data is the original selected Mapping_R transport. -/
theorem closedData_original :
    letI := monoidalData c
    closedData c = CanonicalSourceSmashClosed.Selected.monoidalClosed
      ({ equivalence := c.sourceEquivalence } :
        CanonicalSourceSmash.SourceContext q (EnrichedFunctorCat V J)) := rfl

end PointedCGWH.Spectra.Orthogonal.MMSSStabilization.FunctionIteration.OriginalSelectedPowerData

namespace PointedCGWH.Spectra.Orthogonal.MMSSStabilization.FunctionIteration.FullSourceFreePair
universe uV vV uJ
attribute [local instance] Enriched.prodCategory MonoidalLeftAction.monoidalOppositeLeftAction
attribute [local instance] EnrichedDayKernel.ColimitMonoidal.smallestColimits
variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [SymmetricCategory V] [MonoidalClosed V]
  [Category ℕ] [MonoidalCategory ℕ] [SymmetricCategory ℕ]
  [EnrichedOrdinaryCategory V ℕ] [HasColimitsOfSize.{0, 0} V]
  [HasProducts.{0} V] [HasEqualizers V]
  {q : Enriched.ModuleMappingR.SelectedSource V ℕ}
  {J : Type uJ} [EnrichedCategory V J]
  (c : CanonicalSourceFreeSmash.SelectedPair.Context q J)

/-- The whole independently written family retains the original source instance and both coefficient functors. -/
def IsoFamily : Type _ :=
  OrthogonalSourcePair.SelectedBifunctor.FamilyType c

/-- This whole type is the complete original source family, before any coefficient is selected. -/
theorem family_original : OrthogonalSourcePair.SelectedBifunctor.FamilyType c = IsoFamily c := rfl

/-- The entire actual selected comparison is retained at that independently stated whole family. -/
def comparison : IsoFamily c :=
  OrthogonalSourcePair.SelectedBifunctor.functorIso c

/-- The whole source-family value is exactly the original value, retaining both maps. -/
theorem comparison_original :
    comparison c = OrthogonalSourcePair.SelectedBifunctor.functorIso c := rfl

/-- The full original successor family is written after selecting the source/E instance once. -/
def SuccessorFamilyType (S : ℕ → V) : Type _ :=
  letI := OriginalSelectedPowerData.monoidalData c
  ∀ n : ℕ,
    TypedFullPowerData.object c S 1 ⊗ TypedFullPowerData.object c S n ≅
      TypedFullPowerData.object c S (n + 1)

/-- The same independent full component type on the entire selected source/E structure. -/
def SuccessorComponentType (S : ℕ → V) (n : ℕ) : Type _ :=
  letI := OriginalSelectedPowerData.monoidalData c
  TypedFullPowerData.object c S 1 ⊗ TypedFullPowerData.object c S n ≅
    TypedFullPowerData.object c S (n + 1)

/-- Selecting any degree retains the exact complete original component type. -/
theorem successorFamily_component_type (S : ℕ → V) :
    SuccessorFamilyType c S = (∀ n, SuccessorComponentType c S n) := rfl

/-- The entire original free-pair family and its actual coefficient/degree maps construct every successor. -/
def successor (S : ℕ → V)
    (coefficient : ∀ n, S (c.tensorIndex 1 n) ≅ S 1 ⊗ S n)
    (degree : ∀ n, c.tensorIndex 1 n = n + 1)
    (iso : OrthogonalSourcePair.SelectedBifunctor.FamilyType c) :
    ∀ n, SuccessorComponentType c S n := by
  letI := OriginalSelectedPowerData.monoidalData c
  intro n
  let F : ℕ → V ⥤ EnrichedFunctorCat V J := fun n => Free.functor (c.indexMap n)
  exact (iso 1 n).app (S 1, S n) ≪≫
    (F (c.tensorIndex 1 n)).mapIso (coefficient n).symm ≪≫
    eqToIso (congrArg (fun k => (F k).obj (S (c.tensorIndex 1 n))) (degree n)) ≪≫
    (F (n + 1)).mapIso (eqToIso (congrArg S (degree n)))

end PointedCGWH.Spectra.Orthogonal.MMSSStabilization.FunctionIteration.FullSourceFreePair

end
end CurrentFullFreeSourceBindings

section CompleteOriginalRegularUnitData

set_option autoImplicit false
noncomputable section
universe uRegularUnit vRegularUnit
open CategoryTheory MonoidalCategory Limits
open scoped CategoryTheory.MonObj
namespace PointedCGWH.Spectra.Orthogonal.MMSSStabilization.FunctionIteration.FreeZero
attribute [local instance] MonoidalLeftAction.monoidalOppositeLeftAction
variable {C : Type uRegularUnit} [Category.{vRegularUnit} C] [MonoidalCategory C]
  (R : C) [MonObj R]

/-- Every original full tensor and free-unit comparison gives the complete regular-unit Iso. -/
def regularUnitIso (m : MonoidalCategory (CommutativeModuleConversion.RightModule R)) :
    letI := m
    (RightModuleFree.freeObject R (𝟙_ C) ≅ 𝟙_ (CommutativeModuleConversion.RightModule R)) →
    (RightModuleFree.regularObject R ≅ 𝟙_ (CommutativeModuleConversion.RightModule R)) :=
  letI := m
  fun e => (RightModuleFree.freeUnitRegularIso R).symm ≪≫ e

/-- The forward full carrier comparison retains the original free-unit forward map. -/
theorem regularUnitIso_hom_word (m : MonoidalCategory (CommutativeModuleConversion.RightModule R)) :
    letI := m
    ∀ e : RightModuleFree.freeObject R (𝟙_ C) ≅ 𝟙_ (CommutativeModuleConversion.RightModule R),
      (regularUnitIso R m e).hom.hom = (λ_ R).inv ≫ e.hom.hom := by
  let := m
  intro e
  change ((RightModuleFree.freeUnitRegularIso R).inv ≫ e.hom).hom = _
  rw [Mod.comp_hom', RightModuleFree.freeUnitRegularIso_inv]
  rfl

/-- The inverse full carrier comparison retains the original free-unit inverse map. -/
theorem regularUnitIso_inv_word (m : MonoidalCategory (CommutativeModuleConversion.RightModule R)) :
    letI := m
    ∀ e : RightModuleFree.freeObject R (𝟙_ C) ≅ 𝟙_ (CommutativeModuleConversion.RightModule R),
      (regularUnitIso R m e).inv.hom = e.inv.hom ≫ (λ_ R).hom := by
  let := m
  intro e
  change (e.inv ≫ (RightModuleFree.freeUnitRegularIso R).hom).hom = _
  rw [Mod.comp_hom', RightModuleFree.freeUnitRegularIso_hom]
  rfl

/-- Every original unit-carrier equality retains the complete forward carrier word. -/
theorem regularUnitIso_hom
    (m : MonoidalCategory (CommutativeModuleConversion.RightModule R)) :
    letI := m
    ∀ (e : RightModuleFree.freeObject R (𝟙_ C) ≅ 𝟙_ (CommutativeModuleConversion.RightModule R))
      (h : (𝟙_ (CommutativeModuleConversion.RightModule R)).X = R),
      e.hom.hom = (λ_ R).hom ≫ eqToHom h.symm →
      (regularUnitIso R m e).hom.hom = eqToHom h.symm := by
  let := m
  intro e h he
  rw [regularUnitIso_hom_word, he]
  exact Iso.inv_hom_id_assoc (λ_ R) _

/-- Every original unit-carrier equality retains the complete inverse carrier word. -/
theorem regularUnitIso_inv
    (m : MonoidalCategory (CommutativeModuleConversion.RightModule R)) :
    letI := m
    ∀ (e : RightModuleFree.freeObject R (𝟙_ C) ≅ 𝟙_ (CommutativeModuleConversion.RightModule R))
      (h : (𝟙_ (CommutativeModuleConversion.RightModule R)).X = R),
      e.inv.hom = eqToHom h ≫ (λ_ R).inv →
      (regularUnitIso R m e).inv.hom = eqToHom h := by
  let := m
  intro e h he
  rw [regularUnitIso_inv_word, he]
  change (eqToHom h ≫ (λ_ R).inv) ≫ (λ_ R).hom = eqToHom h
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun q => eqToHom h ≫ q) (Iso.inv_hom_id (λ_ R))).trans
      (Category.comp_id _))





end PointedCGWH.Spectra.Orthogonal.MMSSStabilization.FunctionIteration.FreeZero

end
end CompleteOriginalRegularUnitData

section NativeFreePowerSource
universe uP vP
open CategoryTheory MonoidalCategory MonoidalClosed
open scoped MonoidalClosed

namespace PointedCGWH.Spectra.Orthogonal.MMSSStabilization.FunctionIteration.Powers

variable {C : Type uP} [Category.{vP} C] [MonoidalCategory C] [MonoidalClosed C]

/-- The actual right-associated finite tensor objects, with the original tensor and unit. -/
def rightPower (K : C) : ℕ → C :=
  Nat.rec (𝟙_ C) (fun _ P => K ⊗ P)

/-- Both complete original function maps are iterated through actual internal currying. -/
def functionPowerIso (K : C) : ∀ n : ℕ,
    ihom (rightPower K n) ≅ Functor.Iteration.iterate (ihom K) n :=
  Nat.rec (motive := fun n : ℕ =>
    ihom (rightPower K n) ≅ Functor.Iteration.iterate (ihom K) n)
    unitNatIso.symm (fun n e =>
    OriginalLoopInterchangeGeometry.originalIhomCurryingNatIso K (rightPower K n) ≪≫
      Functor.isoWhiskerLeft (ihom K) e ≪≫
        (Functor.Iteration.iteratePrefixIso (ihom K) n).symm)

/-- The original whole coaugmentation induced by the actual source arrow to the unit. -/
def sourceUnitCoaugmentation {K : C} (l : K ⟶ 𝟙_ C) : 𝟭 C ⟶ ihom K :=
  unitNatIso.hom ≫ pre l

/-- Delete the first original tensor factor by the actual source arrow and actual left unitor. -/
def sourceDrop {K : C} (l : K ⟶ 𝟙_ C) (n : ℕ) :
    rightPower K (n + 1) ⟶ rightPower K n :=
  (l ▷ rightPower K n) ≫ (λ_ (rightPower K n)).hom

/-- Twice uncurrying preserves the original complete associator and evaluation. -/
theorem doubleUncurryPostCurrying (K M : C) {A X : C}
    (f : A ⟶ (ihom (K ⊗ M)).obj X) :
    uncurry (A := K) (uncurry (A := M) (f ≫ ihomCurry K M X)) =
      (α_ K M A).inv ≫ uncurry f := by
  simp only [uncurry_natural_left, uncurry_uncurry_ihomCurry]
  rw [associator_inv_naturality_right_assoc, uncurry_eq]

/-- The original closed unit transpose and the original left unitor give the same currying map. -/
theorem curry_left_unitor (M X : C) :
    (pre (λ_ M).hom).app X ≫ ihomCurry (𝟙_ C) M X =
      (ihom M).map (unitNatIso.hom.app X) := by
  apply uncurry_injective (A := M)
  apply uncurry_injective (A := 𝟙_ C)
  rw [doubleUncurryPostCurrying, uncurry_pre, uncurry_ihom_map,
    uncurry_natural_left,
    CategoryTheory.EnrichedAdjunctionHom.UnitValue.unitNatIso_hom_uncurry]
  exact (leftUnitor_tensor_hom_assoc M ((ihom M).obj X)
    ((ihom.ev M).app X)).symm.trans
      (leftUnitor_naturality ((ihom.ev M).app X)).symm

/-- The complete source-drop map is the actual function image of the original-input unit map. -/
theorem curry_source_drop {K : C} (l : K ⟶ 𝟙_ C) (M X : C) :
    (pre ((l ▷ M) ≫ (λ_ M).hom)).app X ≫ ihomCurry K M X =
      (ihom M).map ((sourceUnitCoaugmentation l).app X) := by
  have hp := congrArg (fun q => q.app X) (pre_map (l ▷ M) (λ_ M).hom)
  change (pre ((l ▷ M) ≫ (λ_ M).hom)).app X ≫ ihomCurry K M X =
    (ihom M).map (unitNatIso.hom.app X ≫ (pre l).app X)
  rw [hp, NatTrans.comp_app, Category.assoc, CategoryTheory.MonoidalClosed.ihomCurry_naturality_first, ← Category.assoc,
    curry_left_unitor, ← (ihom M).map_comp]

/-- Every original source-drop square uses the literal iterated coaugmentation on X. -/
theorem sourceDrop_functionPowerIso {K : C} (l : K ⟶ 𝟙_ C) (n : ℕ) (X : C) :
    (pre (sourceDrop l n)).app X ≫ (functionPowerIso K (n + 1)).hom.app X =
      (functionPowerIso K n).hom.app X ≫
        (Functor.Iteration.inputTransition (sourceUnitCoaugmentation l) n).app X := by
  change (pre ((l ▷ rightPower K n) ≫ (λ_ (rightPower K n)).hom)).app X ≫
    (ihomCurry K (rightPower K n) X ≫
      (functionPowerIso K n).hom.app ((ihom K).obj X) ≫
        (Functor.Iteration.iteratePrefixIso (ihom K) n).inv.app X) = _
  rw [← Category.assoc, ← Category.assoc, curry_source_drop]
  rw [(functionPowerIso K n).hom.naturality ((sourceUnitCoaugmentation l).app X)]
  exact Category.assoc _ _ _

/-- Both full inverse comparison maps retain the same original transition square. -/
theorem sourceDrop_functionPowerIso_inverse {K : C} (l : K ⟶ 𝟙_ C) (n : ℕ) (X : C) :
    (Functor.Iteration.inputTransition (sourceUnitCoaugmentation l) n).app X ≫
        (functionPowerIso K (n + 1)).inv.app X =
      (functionPowerIso K n).inv.app X ≫ (pre (sourceDrop l n)).app X := by
  apply (cancel_epi ((functionPowerIso K n).hom.app X)).1
  rw [← Category.assoc, ← sourceDrop_functionPowerIso, Category.assoc,
    Iso.hom_inv_id_app, Category.comp_id, Iso.hom_inv_id_app_assoc]

end PointedCGWH.Spectra.Orthogonal.MMSSStabilization.FunctionIteration.Powers
section CompleteGenericFreeFamily

set_option autoImplicit false
noncomputable section
universe uC vC
open CategoryTheory MonoidalCategory
open scoped MonoidalClosed

namespace PointedCGWH.Spectra.Orthogonal.MMSSStabilization.FunctionIteration.Powers
variable {C : Type uC} [Category.{vC} C] [MonoidalCategory C] [MonoidalClosed C]


end PointedCGWH.Spectra.Orthogonal.MMSSStabilization.FunctionIteration.Powers

namespace PointedCGWH.Spectra.Orthogonal.MMSSStabilization.FunctionIteration.Powers.FreeFamily
universe uGenericFamily vGenericFamily
variable {C : Type uGenericFamily} [Category.{vGenericFamily} C] [MonoidalCategory C] [MonoidalClosed C]

/-- All original zero and successor free comparisons retain their two source maps. -/
def powerIso (K : C) (P : ℕ → C) (z : 𝟙_ C ≅ P 0)
    (step : ∀ n, K ⊗ P n ≅ P (n + 1)) : ∀ n, rightPower K n ≅ P n :=
  Nat.rec z (fun n e => tensorIso (Iso.refl K) e ≪≫ step n)

/-- Full currying directly along the original free-family tensor comparisons. -/
def functionIso (K : C) (P : ℕ → C) (z : 𝟙_ C ≅ P 0)
    (step : ∀ n, K ⊗ P n ≅ P (n + 1)) : ∀ n,
      ihom (P n) ≅ Functor.Iteration.iterate (ihom K) n :=
  Nat.rec (motive := fun n => ihom (P n) ≅ Functor.Iteration.iterate (ihom K) n)
    (MonoidalClosed.internalHom.mapIso z.op ≪≫ MonoidalClosed.unitNatIso.symm)
    (fun n e => MonoidalClosed.internalHom.mapIso (step n).op ≪≫
      MonoidalClosed.OriginalLoopInterchangeGeometry.originalIhomCurryingNatIso K (P n) ≪≫
      Functor.isoWhiskerLeft (ihom K) e ≪≫
      (Functor.Iteration.iteratePrefixIso (ihom K) n).symm)

/-- The same whole family comparison through its actual tensor source power. -/
def powerFunctionIso (K : C) (P : ℕ → C) (z : 𝟙_ C ≅ P 0)
    (step : ∀ n, K ⊗ P n ≅ P (n + 1)) (n : ℕ) :
      ihom (P n) ≅ Functor.Iteration.iterate (ihom K) n :=
  MonoidalClosed.internalHom.mapIso (powerIso K P z step n).op ≪≫ functionPowerIso K n

/-- Every degree uses precisely the same full free-family maps in the two currying constructions. -/
theorem powerFunctionIso_eq (K : C) (P : ℕ → C) (z : 𝟙_ C ≅ P 0)
    (step : ∀ n, K ⊗ P n ≅ P (n + 1)) (n : ℕ) :
    powerFunctionIso K P z step n = functionIso K P z step n := by
  induction n with
  | zero => rfl
  | succ n hn =>
    apply Iso.ext
    apply NatTrans.ext
    funext X
    let a : (ihom (P (n + 1))).obj X ⟶ (ihom (K ⊗ P n)).obj X :=
      (MonoidalClosed.pre (step n).hom).app X
    let b : (ihom (K ⊗ P n)).obj X ⟶ (ihom (K ⊗ rightPower K n)).obj X :=
      (MonoidalClosed.pre (K ◁ (powerIso K P z step n).hom)).app X
    let c : (ihom (K ⊗ rightPower K n)).obj X ⟶
        (ihom (rightPower K n)).obj ((ihom K).obj X) :=
      MonoidalClosed.ihomCurry K (rightPower K n) X
    let c' : (ihom (K ⊗ P n)).obj X ⟶ (ihom (P n)).obj ((ihom K).obj X) :=
      MonoidalClosed.ihomCurry K (P n) X
    let b' : (ihom (P n)).obj ((ihom K).obj X) ⟶
        (ihom (rightPower K n)).obj ((ihom K).obj X) :=
      (MonoidalClosed.pre (powerIso K P z step n).hom).app ((ihom K).obj X)
    let d : (ihom (rightPower K n)).obj ((ihom K).obj X) ⟶
        (Functor.Iteration.iterate (ihom K) n).obj ((ihom K).obj X) :=
      (functionPowerIso K n).hom.app ((ihom K).obj X)
    let d' : (ihom (P n)).obj ((ihom K).obj X) ⟶
        (Functor.Iteration.iterate (ihom K) n).obj ((ihom K).obj X) :=
      (functionIso K P z step n).hom.app ((ihom K).obj X)
    let r : (Functor.Iteration.iterate (ihom K) n).obj ((ihom K).obj X) ⟶
        (Functor.Iteration.iterate (ihom K) (n + 1)).obj X :=
      (Functor.Iteration.iteratePrefixIso (ihom K) n).inv.app X
    let p : (ihom (P (n + 1))).obj X ⟶ (ihom (K ⊗ rightPower K n)).obj X :=
      (MonoidalClosed.pre (powerIso K P z step (n + 1)).hom).app X
    have hsource : (powerIso K P z step (n + 1)).hom =
        (K ◁ (powerIso K P z step n).hom) ≫ (step n).hom :=
      congrArg (fun f => f ≫ (step n).hom) (id_tensorHom K (powerIso K P z step n).hom)
    have hp : p = a ≫ b :=
      (congrArg (fun f => (MonoidalClosed.pre f).app X) hsource).trans
        (congrArg (fun t => t.app X)
          (MonoidalClosed.pre_map (K ◁ (powerIso K P z step n).hom) (step n).hom))
    have hcurr : b ≫ c = c' ≫ b' :=
      CategoryTheory.MonoidalClosed.ihomCurry_naturality_second K (powerIso K P z step n).hom X
    have hprev : b' ≫ d = d' :=
      congrArg (fun e => e.hom.app ((ihom K).obj X)) hn
    have hbc : b ≫ c ≫ d = c' ≫ d' :=
      (Category.assoc b c d).symm.trans
        ((congrArg (fun f => f ≫ d) hcurr).trans
          ((Category.assoc c' b' d).trans (congrArg (fun f => c' ≫ f) hprev)))
    have hword : (a ≫ b) ≫ c ≫ d ≫ r = a ≫ c' ≫ d' ≫ r := by
      calc
        (a ≫ b) ≫ c ≫ d ≫ r = a ≫ (b ≫ c ≫ d) ≫ r := by
          simp only [Category.assoc]
        _ = a ≫ (c' ≫ d') ≫ r := congrArg (fun f => a ≫ f ≫ r) hbc
        _ = a ≫ c' ≫ d' ≫ r := by simp only [Category.assoc]
    have hleft : (powerFunctionIso K P z step (n + 1)).hom.app X = p ≫ c ≫ d ≫ r := rfl
    have hright : (functionIso K P z step (n + 1)).hom.app X = a ≫ c' ≫ d' ≫ r := rfl
    exact hleft.trans
      (((congrArg (fun f => f ≫ c ≫ d ≫ r) hp).trans hword).trans hright.symm)


/-- The original source arrow deletes the first free factor through the entire free comparison. -/
def familyDrop (K : C) (P : ℕ → C) (step : ∀ n, K ⊗ P n ≅ P (n + 1))
    (l : K ⟶ 𝟙_ C) (n : ℕ) : P (n + 1) ⟶ P n :=
  (step n).inv ≫ (l ▷ P n) ≫ (λ_ (P n)).hom

omit [MonoidalClosed C] in
private theorem tensorDropSquare {K U V W : C} (e : U ≅ V) (step : K ⊗ V ≅ W)
    (l : K ⟶ 𝟙_ C) :
    (tensorIso (Iso.refl K) e ≪≫ step).hom ≫
        (step.inv ≫ (l ▷ V) ≫ (λ_ V).hom) =
      ((l ▷ U) ≫ (λ_ U).hom) ≫ e.hom := by
  simp only [Iso.trans_hom, tensorIso_hom, Iso.refl_hom, Category.assoc,
    Iso.hom_inv_id_assoc, id_tensorHom]
  rw [← Category.assoc, whisker_exchange, Category.assoc, leftUnitor_naturality]

omit [MonoidalClosed C] in
/-- The complete original source drop commutes with both original source-power comparisons. -/
theorem familyDrop_powerIso (K : C) (P : ℕ → C) (z : 𝟙_ C ≅ P 0)
    (step : ∀ n, K ⊗ P n ≅ P (n + 1)) (l : K ⟶ 𝟙_ C) (n : ℕ) :
    (powerIso K P z step (n + 1)).hom ≫ familyDrop K P step l n =
      sourceDrop l n ≫ (powerIso K P z step n).hom :=
  tensorDropSquare (powerIso K P z step n) (step n) l

/-- Both full function constructions preserve the literal source drop and the original-input unit. -/
theorem familyDrop_functionIso (K : C) (P : ℕ → C) (z : 𝟙_ C ≅ P 0)
    (step : ∀ n, K ⊗ P n ≅ P (n + 1)) (l : K ⟶ 𝟙_ C) (n : ℕ) (X : C) :
    (MonoidalClosed.pre (familyDrop K P step l n)).app X ≫
        (functionIso K P z step (n + 1)).hom.app X =
      (functionIso K P z step n).hom.app X ≫
        (Functor.Iteration.inputTransition (sourceUnitCoaugmentation l) n).app X := by
  let a := (MonoidalClosed.pre (familyDrop K P step l n)).app X
  let b := (MonoidalClosed.pre (powerIso K P z step (n + 1)).hom).app X
  let c := (MonoidalClosed.pre (powerIso K P z step n).hom).app X
  let d := (MonoidalClosed.pre (sourceDrop l n)).app X
  let e := (functionPowerIso K n).hom.app X
  let e' := (functionPowerIso K (n + 1)).hom.app X
  let t := (Functor.Iteration.inputTransition (sourceUnitCoaugmentation l) n).app X
  have hRaw := congrArg (fun f => (MonoidalClosed.pre f).app X)
    (familyDrop_powerIso K P z step l n)
  rw [MonoidalClosed.pre_map, MonoidalClosed.pre_map, NatTrans.comp_app,
    NatTrans.comp_app] at hRaw
  have hSource : a ≫ b = c ≫ d := hRaw
  have hPower : d ≫ e' = e ≫ t := sourceDrop_functionPowerIso l n X
  have hSquare : a ≫ (powerFunctionIso K P z step (n + 1)).hom.app X =
      (powerFunctionIso K P z step n).hom.app X ≫ t := by
    calc
      a ≫ (powerFunctionIso K P z step (n + 1)).hom.app X = a ≫ b ≫ e' := rfl
      _ = (a ≫ b) ≫ e' := (Category.assoc a b e').symm
      _ = (c ≫ d) ≫ e' := congrArg (fun f => f ≫ e') hSource
      _ = c ≫ d ≫ e' := Category.assoc c d e'
      _ = c ≫ e ≫ t := congrArg (fun f => c ≫ f) hPower
      _ = (c ≫ e) ≫ t := (Category.assoc c e t).symm
      _ = (powerFunctionIso K P z step n).hom.app X ≫ t := rfl
  have hNext := congrArg (fun iso => a ≫ iso.hom.app X)
    (powerFunctionIso_eq K P z step (n + 1))
  have hCurrent := congrArg (fun iso => iso.hom.app X ≫ t)
    (powerFunctionIso_eq K P z step n)
  exact hNext.symm.trans (hSquare.trans hCurrent)

/-- Both inverse function maps commute with precisely the same original source arrows. -/
theorem familyDrop_functionIso_inv (K : C) (P : ℕ → C) (z : 𝟙_ C ≅ P 0)
    (step : ∀ n, K ⊗ P n ≅ P (n + 1)) (l : K ⟶ 𝟙_ C) (n : ℕ) (X : C) :
    (Functor.Iteration.inputTransition (sourceUnitCoaugmentation l) n).app X ≫
        (functionIso K P z step (n + 1)).inv.app X =
      (functionIso K P z step n).inv.app X ≫
        (MonoidalClosed.pre (familyDrop K P step l n)).app X := by
  apply (cancel_epi ((functionIso K P z step n).hom.app X)).1
  rw [← Category.assoc, ← familyDrop_functionIso, Category.assoc,
    Iso.hom_inv_id_app, Category.comp_id, Iso.hom_inv_id_app_assoc]

/-- The actual original free-source function values and their complete source-drop arrows. -/
def diagram (K : C) (P : ℕ → C) (step : ∀ n, K ⊗ P n ≅ P (n + 1))
    (l : K ⟶ 𝟙_ C) (X : C) : ℕ ⥤ C :=
  Functor.ofSequence (X := fun n => (ihom (P n)).obj X)
    (fun n => (MonoidalClosed.pre (familyDrop K P step l n)).app X)

/-- Both original function maps compare the complete original-input and actual free-source diagrams. -/
def diagramIso (K : C) (P : ℕ → C) (z : 𝟙_ C ≅ P 0)
    (step : ∀ n, K ⊗ P n ≅ P (n + 1)) (l : K ⟶ 𝟙_ C) (X : C) :
    diagram K P step l X ≅ Functor.Iteration.inputDiagram (sourceUnitCoaugmentation l) X where
  hom := NatTrans.ofSequence (fun n => (functionIso K P z step n).hom.app X)
    (fun n => by
      have hs : (diagram K P step l X).map (homOfLE (Nat.le_succ n)) =
          (MonoidalClosed.pre (familyDrop K P step l n)).app X :=
        Functor.ofSequence_map_homOfLE_succ _ n
      have ht := Functor.Iteration.inputDiagram_map_succ (sourceUnitCoaugmentation l) X n
      exact (congrArg (fun f => f ≫ (functionIso K P z step (n + 1)).hom.app X) hs).trans
        ((familyDrop_functionIso K P z step l n X).trans
          (congrArg (fun f => (functionIso K P z step n).hom.app X ≫ f) ht.symm)))
  inv := NatTrans.ofSequence (fun n => (functionIso K P z step n).inv.app X)
    (fun n => by
      have hs : (diagram K P step l X).map (homOfLE (Nat.le_succ n)) =
          (MonoidalClosed.pre (familyDrop K P step l n)).app X :=
        Functor.ofSequence_map_homOfLE_succ _ n
      have ht := Functor.Iteration.inputDiagram_map_succ (sourceUnitCoaugmentation l) X n
      exact (congrArg (fun f => f ≫ (functionIso K P z step (n + 1)).inv.app X) ht).trans
        ((familyDrop_functionIso_inv K P z step l n X).trans
          (congrArg (fun f => (functionIso K P z step n).inv.app X ≫ f) hs.symm)))
  hom_inv_id := by
    apply NatTrans.ext
    funext n
    exact (functionIso K P z step n).hom_inv_id_app X
  inv_hom_id := by
    apply NatTrans.ext
    funext n
    exact (functionIso K P z step n).inv_hom_id_app X


/-- Every original input map acts by its entire source-function map at every stage. -/
def diagramMap (K : C) (P : ℕ → C) (step : ∀ n, K ⊗ P n ≅ P (n + 1))
    (l : K ⟶ 𝟙_ C) {X Y : C} (f : X ⟶ Y) :
    diagram K P step l X ⟶ diagram K P step l Y :=
  NatTrans.ofSequence (fun n => (ihom (P n)).map f) (fun n => by
    have hX : (diagram K P step l X).map (homOfLE (Nat.le_succ n)) =
        (MonoidalClosed.pre (familyDrop K P step l n)).app X :=
      Functor.ofSequence_map_homOfLE_succ _ n
    have hY : (diagram K P step l Y).map (homOfLE (Nat.le_succ n)) =
        (MonoidalClosed.pre (familyDrop K P step l n)).app Y :=
      Functor.ofSequence_map_homOfLE_succ _ n
    exact (congrArg (fun g => g ≫ (ihom (P (n + 1))).map f) hX).trans
      (((MonoidalClosed.pre (familyDrop K P step l n)).naturality f).symm.trans
        (congrArg (fun g => (ihom (P n)).map f ≫ g) hY.symm)))

/-- The complete actual source-function diagrams are functorial in all original inputs. -/
def diagramFunctor (K : C) (P : ℕ → C) (step : ∀ n, K ⊗ P n ≅ P (n + 1))
    (l : K ⟶ 𝟙_ C) : C ⥤ (ℕ ⥤ C) where
  obj := diagram K P step l
  map := diagramMap K P step l
  map_id X := by
    apply NatTrans.ext
    funext n
    exact (ihom (P n)).map_id X
  map_comp f g := by
    apply NatTrans.ext
    funext n
    exact (ihom (P n)).map_comp f g

/-- Both full diagram comparison maps are natural on every complete original input arrow. -/
def diagramNatIso (K : C) (P : ℕ → C) (z : 𝟙_ C ≅ P 0)
    (step : ∀ n, K ⊗ P n ≅ P (n + 1)) (l : K ⟶ 𝟙_ C) :
    diagramFunctor K P step l ≅ Functor.Iteration.inputDiagramFunctor (sourceUnitCoaugmentation l) :=
  NatIso.ofComponents (diagramIso K P z step l) (fun f => by
    apply NatTrans.ext
    funext n
    exact (functionIso K P z step n).hom.naturality f)

/-- Every forward stage is the complete original free-source function comparison. -/
theorem diagramIso_hom_app (K : C) (P : ℕ → C) (z : 𝟙_ C ≅ P 0)
    (step : ∀ n, K ⊗ P n ≅ P (n + 1)) (l : K ⟶ 𝟙_ C) (X : C) (n : ℕ) :
    (diagramIso K P z step l X).hom.app n = (functionIso K P z step n).hom.app X := rfl

/-- Every inverse stage retains the complete original inverse source-function map. -/
theorem diagramIso_inv_app (K : C) (P : ℕ → C) (z : 𝟙_ C ≅ P 0)
    (step : ∀ n, K ⊗ P n ≅ P (n + 1)) (l : K ⟶ 𝟙_ C) (X : C) (n : ℕ) :
    (diagramIso K P z step l X).inv.app n = (functionIso K P z step n).inv.app X := rfl

end PointedCGWH.Spectra.Orthogonal.MMSSStabilization.FunctionIteration.Powers.FreeFamily

end
end CompleteGenericFreeFamily


section AbstractFullSourcePowerCompatibility
noncomputable section
universe uFullPowerCompatibility vFullPowerCompatibility
open CategoryTheory MonoidalCategory
open scoped MonoidalClosed

namespace PointedCGWH.Spectra.Orthogonal.MMSSStabilization.FunctionIteration.Powers.FullCompatibility

variable {C : Type uFullPowerCompatibility} [Category.{vFullPowerCompatibility} C]
  [MonoidalCategory C] [MonoidalClosed C]

/-- The full ordinary source-power family type is stated before every comparison proof. -/
def PowerFamilyType (K : C) (P : ℕ → C) : Type _ :=
  ∀ n, rightPower K n ≅ P n

/-- The entire ordinary source-function family type retains all actual internal-Hom maps. -/
def FunctionFamilyType (K : C) (P : ℕ → C) : Type _ :=
  ∀ n, ihom (P n) ≅ Functor.Iteration.iterate (ihom K) n

/-- Every source-power square is on the original source-unit arrow and complete Iso family. -/
def PowerDrop (K : C) (P : ℕ → C) (e : PowerFamilyType K P)
    (d : ∀ n, P (n + 1) ⟶ P n) (l : K ⟶ 𝟙_ C) : Prop :=
  ∀ n, (e (n + 1)).hom ≫ d n = sourceDrop l n ≫ (e n).hom

/-- The inverse source-power square retains the same original source arrows and two inverse maps. -/
def PowerDropInverse (K : C) (P : ℕ → C) (e : PowerFamilyType K P)
    (d : ∀ n, P (n + 1) ⟶ P n) (l : K ⟶ 𝟙_ C) : Prop :=
  ∀ n, d n ≫ (e n).inv = (e (n + 1)).inv ≫ sourceDrop l n

/-- The full function square is stated on every degree and every original target object. -/
def FunctionDrop (K : C) (P : ℕ → C) (F : FunctionFamilyType K P)
    (d : ∀ n, P (n + 1) ⟶ P n) (l : K ⟶ 𝟙_ C) : Prop :=
  ∀ n X, (MonoidalClosed.pre (d n)).app X ≫ (F (n + 1)).hom.app X =
    (F n).hom.app X ≫ (Functor.Iteration.inputTransition (sourceUnitCoaugmentation l) n).app X

/-- Every inverse function square retains those same original source and target parameters. -/
def FunctionDropInverse (K : C) (P : ℕ → C) (F : FunctionFamilyType K P)
    (d : ∀ n, P (n + 1) ⟶ P n) (l : K ⟶ 𝟙_ C) : Prop :=
  ∀ n X, (Functor.Iteration.inputTransition (sourceUnitCoaugmentation l) n).app X ≫
      (F (n + 1)).inv.app X = (F n).inv.app X ≫ (MonoidalClosed.pre (d n)).app X

/-- Forward naturality retains every whole original target arrow at every source degree. -/
def HomNaturality (K : C) (P : ℕ → C) (F : FunctionFamilyType K P) : Prop :=
  ∀ n {X Y : C} (f : X ⟶ Y), (ihom (P n)).map f ≫ (F n).hom.app Y =
    (F n).hom.app X ≫ (Functor.Iteration.iterate (ihom K) n).map f

/-- Inverse naturality is stated on the same actual whole target arrows and source degrees. -/
def InvNaturality (K : C) (P : ℕ → C) (F : FunctionFamilyType K P) : Prop :=
  ∀ n {X Y : C} (f : X ⟶ Y), (Functor.Iteration.iterate (ihom K) n).map f ≫
      (F n).inv.app Y = (F n).inv.app X ≫ (ihom (P n)).map f

omit [MonoidalClosed C] in
/-- The original complete free family gives every source-power compatibility equation. -/
theorem freePowerDrop (K : C) (P : ℕ → C) (z : 𝟙_ C ≅ P 0)
    (step : ∀ n, K ⊗ P n ≅ P (n + 1)) (l : K ⟶ 𝟙_ C) :
    PowerDrop K P (FreeFamily.powerIso K P z step) (FreeFamily.familyDrop K P step l) l := by
  intro n
  exact FreeFamily.familyDrop_powerIso K P z step l n

omit [MonoidalCategory C] [MonoidalClosed C] in
/-- A genuine original Iso square has the full inverse square on the same four endpoints. -/
theorem inverseIsoSquare {A B A' B' : C} (e : A ≅ B) (e' : A' ≅ B')
    (d : B ⟶ B') (r : A ⟶ A') (h : e.hom ≫ d = r ≫ e'.hom) :
    d ≫ e'.inv = e.inv ≫ r := by
  calc
    d ≫ e'.inv = (e.inv ≫ e.hom) ≫ d ≫ e'.inv := by
      rw [e.inv_hom_id, Category.id_comp]
    _ = e.inv ≫ (e.hom ≫ d) ≫ e'.inv := by simp only [Category.assoc]
    _ = e.inv ≫ (r ≫ e'.hom) ≫ e'.inv :=
      congrArg (fun f => e.inv ≫ f ≫ e'.inv) h
    _ = e.inv ≫ r := by simp only [Category.assoc, e'.hom_inv_id, Category.comp_id]

omit [MonoidalClosed C] in
/-- The complete original inverse power square is proved on the same entire source-power family. -/
theorem freePowerDropInverse (K : C) (P : ℕ → C) (z : 𝟙_ C ≅ P 0)
    (step : ∀ n, K ⊗ P n ≅ P (n + 1)) (l : K ⟶ 𝟙_ C) :
    PowerDropInverse K P (FreeFamily.powerIso K P z step)
      (FreeFamily.familyDrop K P step l) l := by
  intro n
  exact inverseIsoSquare (FreeFamily.powerIso K P z step (n + 1))
    (FreeFamily.powerIso K P z step n) (FreeFamily.familyDrop K P step l n)
    (sourceDrop l n) (FreeFamily.familyDrop_powerIso K P z step l n)

/-- The actual original generic source family gives the complete direct-currying drop equations. -/
theorem freeFunctionDrop (K : C) (P : ℕ → C) (z : 𝟙_ C ≅ P 0)
    (step : ∀ n, K ⊗ P n ≅ P (n + 1)) (l : K ⟶ 𝟙_ C) :
    FunctionDrop K P (FreeFamily.functionIso K P z step)
      (FreeFamily.familyDrop K P step l) l := by
  intro n X
  exact FreeFamily.familyDrop_functionIso K P z step l n X

/-- Both direct-currying inverse maps use the same original full source-unit transition. -/
theorem freeFunctionDropInverse (K : C) (P : ℕ → C) (z : 𝟙_ C ≅ P 0)
    (step : ∀ n, K ⊗ P n ≅ P (n + 1)) (l : K ⟶ 𝟙_ C) :
    FunctionDropInverse K P (FreeFamily.functionIso K P z step)
      (FreeFamily.familyDrop K P step l) l := by
  intro n X
  exact FreeFamily.familyDrop_functionIso_inv K P z step l n X

/-- Both original entire source-function constructions give the same family before projection. -/
theorem freeFunctionFamilyEquality (K : C) (P : ℕ → C) (z : 𝟙_ C ≅ P 0)
    (step : ∀ n, K ⊗ P n ≅ P (n + 1)) :
    FreeFamily.functionIso K P z step = FreeFamily.powerFunctionIso K P z step := by
  funext n
  exact (FreeFamily.powerFunctionIso_eq K P z step n).symm

/-- Every original power-function square follows from equality of the entire source-function families. -/
theorem freePowerFunctionDrop (K : C) (P : ℕ → C) (z : 𝟙_ C ≅ P 0)
    (step : ∀ n, K ⊗ P n ≅ P (n + 1)) (l : K ⟶ 𝟙_ C) :
    FunctionDrop K P (FreeFamily.powerFunctionIso K P z step)
      (FreeFamily.familyDrop K P step l) l := by
  rw [← freeFunctionFamilyEquality]
  exact freeFunctionDrop K P z step l

/-- The full inverse power-function square retains both original comparison maps. -/
theorem freePowerFunctionDropInverse (K : C) (P : ℕ → C) (z : 𝟙_ C ≅ P 0)
    (step : ∀ n, K ⊗ P n ≅ P (n + 1)) (l : K ⟶ 𝟙_ C) :
    FunctionDropInverse K P (FreeFamily.powerFunctionIso K P z step)
      (FreeFamily.familyDrop K P step l) l := by
  rw [← freeFunctionFamilyEquality]
  exact freeFunctionDropInverse K P z step l

/-- Every original complete Iso family is forward natural on every target arrow. -/
theorem homNaturality (K : C) (P : ℕ → C) (F : FunctionFamilyType K P) :
    HomNaturality K P F := by
  intro n X Y f
  exact (F n).hom.naturality f

/-- Every original complete Iso family is inverse natural on the same target arrows. -/
theorem invNaturality (K : C) (P : ℕ → C) (F : FunctionFamilyType K P) :
    InvNaturality K P F := by
  intro n X Y f
  exact (F n).inv.naturality f

end PointedCGWH.Spectra.Orthogonal.MMSSStabilization.FunctionIteration.Powers.FullCompatibility
end
end AbstractFullSourcePowerCompatibility

section FullTypedSourcePowerData
set_option autoImplicit false
noncomputable section
universe uV vV uJ
open CategoryTheory MonoidalCategory Limits
open CategoryTheory.EnrichedFunctorCat
open PointedCGWH.Spectra.Orthogonal
open PointedCGWH.Spectra.NativeStableMonoidal
open scoped CategoryTheory.MonObj MonoidalClosed
attribute [local instance] Enriched.prodCategory MonoidalLeftAction.monoidalOppositeLeftAction
attribute [local instance] EnrichedDayKernel.ColimitMonoidal.smallestColimits

namespace PointedCGWH.Spectra.Orthogonal.MMSSStabilization.FunctionIteration.TypedFullPowerData
variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [SymmetricCategory V] [MonoidalClosed V]
  [Category ℕ] [MonoidalCategory ℕ] [SymmetricCategory ℕ]
  [EnrichedOrdinaryCategory V ℕ] [HasColimitsOfSize.{0, 0} V]
  [HasProducts.{0} V] [HasEqualizers V]
  {q : Enriched.ModuleMappingR.SelectedSource V ℕ}
  {J : Type uJ} [EnrichedCategory V J]
  (c : CanonicalSourceFreeSmash.SelectedPair.Context q J)

/-- Both original zero-source maps are retained on the selected actual native tensor. -/
def ZeroType (S : ℕ → V) : Type _ :=
  letI := OriginalSelectedPowerData.monoidalData c
  𝟙_ (EnrichedFunctorCat V J) ≅ object c S 0

/-- Construct the zero source from the same actual E, original Day unit and original coefficient unit. -/
def zero (S : ℕ → V)
    (dayUnit : letI := q.dayMonoidal; Free.object (0 : ℕ) (𝟙_ V) ≅ 𝟙_ (EnrichedFunctorCat V ℕ))
    (scalarUnit : 𝟙_ V ≅ S 0) : ZeroType c S := by
  letI := q.moduleMonoidal
  letI := OriginalSelectedPowerData.monoidalData c
  let u : CanonicalSourceSmashUnit.TypedSource.UnitComparison q J :=
    { equivalence := c.sourceEquivalence
      sourceIndex := 0
      targetIndex := c.indexMap 0
      coefficientUnitIso := dayUnit
      evaluationComparison := c.evaluationComparison 0 }
  exact CanonicalSourceSmashUnit.TypedSource.unitIso u ≪≫
    (Free.functor (c.indexMap 0)).mapIso scalarUnit

/-- The complete original zero and successor free maps, with the source instance bound once. -/
structure Data (S : ℕ → V) where
  /-- Both original maps identify the actual zero source with the same native tensor unit. -/
  zero : ZeroType c S
  /-- Every original degree retains the complete native free-source successor comparison. -/
  successor :
    letI := OriginalSelectedPowerData.monoidalData c
    ∀ n : ℕ, @Iso.{max uJ vV, max (max uJ vV) uV} (EnrichedFunctorCat V J) _
      (object c S 1 ⊗ object c S n) (object c S (n + 1))

/-- The independently stated full function type retains the original closed choice and every free functor. -/
def SuccessorFunctionType (S : ℕ → V) (n : ℕ) : Type _ :=
  letI := OriginalSelectedPowerData.monoidalData c
  letI := OriginalSelectedPowerData.closedData c
  ihom (object c S (n + 1)) ≅ ihom (object c S 1) ⋙ ihom (object c S n)

/-- Full source currying uses the complete original successor map on that same source/E structure. -/
def successorFunction (S : ℕ → V) (data : Data c S) : ∀ n, SuccessorFunctionType c S n := by
  letI := OriginalSelectedPowerData.monoidalData c
  letI := OriginalSelectedPowerData.closedData c
  intro n
  exact MonoidalClosed.internalHom.mapIso (data.successor n).op ≪≫
    MonoidalClosed.OriginalLoopInterchangeGeometry.originalIhomCurryingNatIso
      (object c S 1) (object c S n)

/-- All original tensor powers are compared at a complete independently written native/source type. -/
def PowerType (S : ℕ → V) (n : ℕ) : Type _ :=
  letI := OriginalSelectedPowerData.monoidalData c
  Powers.rightPower (object c S 1) n ≅ object c S n

/-- The full original function functor is retained before every iterate or projection. -/
def FunctionType (S : ℕ → V) (n : ℕ) : Type _ :=
  letI := OriginalSelectedPowerData.monoidalData c
  letI := OriginalSelectedPowerData.closedData c
  ihom (object c S n) ≅ Functor.Iteration.iterate (ihom (object c S 1)) n

/-- The entire original source arrow type uses that same actual tensor unit. -/
def UnitArrowType (S : ℕ → V) : Type _ :=
  letI := OriginalSelectedPowerData.monoidalData c
  object c S 1 ⟶ 𝟙_ (EnrichedFunctorCat V J)

/-- Every original source-drop arrow has its complete native free-spectrum endpoints. -/
def DropType (S : ℕ → V) (n : ℕ) : Type _ := object c S (n + 1) ⟶ object c S n

/-- The entire original free-pair recurrence constructs all full source powers before native application. -/
def power (S : ℕ → V) (data : Data c S) : ∀ n, PowerType c S n := by
  letI := OriginalSelectedPowerData.monoidalData c
  intro n
  exact Powers.FreeFamily.powerIso (object c S 1) (object c S) data.zero data.successor n

/-- The full original currying recurrence constructs every source function functor in the same context. -/
def function (S : ℕ → V) (data : Data c S) : ∀ n, FunctionType c S n := by
  letI := OriginalSelectedPowerData.monoidalData c
  letI := OriginalSelectedPowerData.closedData c
  intro n
  exact Powers.FreeFamily.functionIso (object c S 1) (object c S) data.zero data.successor n

/-- Both original source-power maps and original currying give the full alternative function family. -/
def powerFunction (S : ℕ → V) (data : Data c S) : ∀ n, FunctionType c S n := by
  letI := OriginalSelectedPowerData.monoidalData c
  letI := OriginalSelectedPowerData.closedData c
  intro n
  exact Powers.FreeFamily.powerFunctionIso (object c S 1) (object c S) data.zero data.successor n

/-- The actual original source arrow deletes every first free sphere through the same entire source pair. -/
def drop (S : ℕ → V) (data : Data c S) (l : UnitArrowType c S) : ∀ n, DropType c S n := by
  letI := OriginalSelectedPowerData.monoidalData c
  intro n
  exact Powers.FreeFamily.familyDrop (object c S 1) (object c S) data.successor l n


/-- The full successor function formula binds the original tensor, closed choice and object family first. -/
def OriginalSuccessorFunctionFormula
    (source : CanonicalSourceSmash.SourceContext q (EnrichedFunctorCat V J))
    (P : ℕ → EnrichedFunctorCat V J) : Type _ :=
  letI := source.monoidalCategory
  letI := CanonicalSourceSmashClosed.Selected.monoidalClosed source
  ∀ n : ℕ, ihom (P (n + 1)) ≅ ihom (P 1) ⋙ ihom (P n)

/-- The original complete power formula keeps the same actual tensor and every coefficient object. -/
def OriginalPowerFormula
    (source : CanonicalSourceSmash.SourceContext q (EnrichedFunctorCat V J))
    (P : ℕ → EnrichedFunctorCat V J) : Type _ :=
  letI := source.monoidalCategory
  ∀ n : ℕ, Powers.rightPower (P 1) n ≅ P n

/-- The original full function formula keeps every source label and the entire iterated closed functor. -/
def OriginalFunctionFormula
    (source : CanonicalSourceSmash.SourceContext q (EnrichedFunctorCat V J))
    (P : ℕ → EnrichedFunctorCat V J) : Type _ :=
  letI := source.monoidalCategory
  letI := CanonicalSourceSmashClosed.Selected.monoidalClosed source
  ∀ n : ℕ, ihom (P n) ≅ Functor.Iteration.iterate (ihom (P 1)) n

/-- The complete original unit-arrow formula uses the actual source tensor unit. -/
def OriginalUnitArrowFormula
    (source : CanonicalSourceSmash.SourceContext q (EnrichedFunctorCat V J))
    (P : ℕ → EnrichedFunctorCat V J) : Type _ :=
  letI := source.monoidalCategory
  P 1 ⟶ 𝟙_ (EnrichedFunctorCat V J)

/-- Every original source-drop endpoint is retained as one full source family. -/
def OriginalDropFormula (P : ℕ → EnrichedFunctorCat V J) : Type _ :=
  ∀ n : ℕ, P (n + 1) ⟶ P n

/-- The independently stated successor types are the complete original family before native application. -/
theorem successorFunctionType_original (S : ℕ → V) :
    (∀ n, SuccessorFunctionType c S n) =
      OriginalSuccessorFunctionFormula (sourceContext c) (object c S) := rfl

/-- The independently stated power types are the complete original family on the same source data. -/
theorem powerType_original (S : ℕ → V) :
    (∀ n, PowerType c S n) = OriginalPowerFormula (sourceContext c) (object c S) := rfl

/-- The independently stated function types are the complete original family, including all maps. -/
theorem functionType_original (S : ℕ → V) :
    (∀ n, FunctionType c S n) = OriginalFunctionFormula (sourceContext c) (object c S) := rfl

/-- The independently stated source-unit arrow type is exactly the original one. -/
theorem unitArrowType_original (S : ℕ → V) :
    UnitArrowType c S = OriginalUnitArrowFormula (sourceContext c) (object c S) := rfl

/-- The independently stated source-drop types retain every original endpoint. -/
theorem dropType_original (S : ℕ → V) :
    (∀ n, DropType c S n) = OriginalDropFormula (object c S) := rfl

end PointedCGWH.Spectra.Orthogonal.MMSSStabilization.FunctionIteration.TypedFullPowerData
end
end FullTypedSourcePowerData



section FullTypedSourcePowerCompatibility
noncomputable section
universe uTypedCompatibilityV vTypedCompatibilityV uTypedCompatibilityJ
open CategoryTheory MonoidalCategory Limits
open CategoryTheory.EnrichedFunctorCat
open PointedCGWH.Spectra.Orthogonal
open scoped CategoryTheory.MonObj MonoidalClosed
attribute [local instance] Enriched.prodCategory MonoidalLeftAction.monoidalOppositeLeftAction
attribute [local instance] EnrichedDayKernel.ColimitMonoidal.smallestColimits

namespace PointedCGWH.Spectra.Orthogonal.MMSSStabilization.FunctionIteration.TypedFullPowerData

variable {V : Type uTypedCompatibilityV} [Category.{vTypedCompatibilityV} V] [MonoidalCategory V]
  [SymmetricCategory V] [MonoidalClosed V]
  [Category ℕ] [MonoidalCategory ℕ] [SymmetricCategory ℕ]
  [EnrichedOrdinaryCategory V ℕ] [HasColimitsOfSize.{0, 0} V]
  [HasProducts.{0} V] [HasEqualizers V]
  {q : Enriched.ModuleMappingR.SelectedSource V ℕ}
  {J : Type uTypedCompatibilityJ} [EnrichedCategory V J]
  (c : CanonicalSourceFreeSmash.SelectedPair.Context q J)

/-- Equality of both complete source-function families on the original selected source context. -/
def FunctionFamilyEquality (S : ℕ → V) (data : Data c S) : Prop :=
  function c S data = powerFunction c S data

/-- Every original source-unit arrow and every source-power stage retain the full drop square. -/
def PowerDropCompatibility (S : ℕ → V) (data : Data c S) : Prop :=
  letI := OriginalSelectedPowerData.monoidalData c
  ∀ l : UnitArrowType c S,
    Powers.FullCompatibility.PowerDrop (object c S 1) (object c S) (power c S data) (drop c S data l) l

/-- Both inverse source-power maps retain the same original full drop arrow. -/
def PowerDropInverseCompatibility (S : ℕ → V) (data : Data c S) : Prop :=
  letI := OriginalSelectedPowerData.monoidalData c
  ∀ l : UnitArrowType c S,
    Powers.FullCompatibility.PowerDropInverse (object c S 1) (object c S) (power c S data) (drop c S data l) l

/-- The full original direct-currying maps preserve every original source drop and target object. -/
def FunctionDropCompatibility (S : ℕ → V) (data : Data c S) : Prop :=
  letI := OriginalSelectedPowerData.monoidalData c
  letI := OriginalSelectedPowerData.closedData c
  ∀ l : UnitArrowType c S,
    Powers.FullCompatibility.FunctionDrop (object c S 1) (object c S) (function c S data) (drop c S data l) l

/-- Every inverse direct-currying map retains the same original transition and source drop. -/
def FunctionDropInverseCompatibility (S : ℕ → V) (data : Data c S) : Prop :=
  letI := OriginalSelectedPowerData.monoidalData c
  letI := OriginalSelectedPowerData.closedData c
  ∀ l : UnitArrowType c S,
    Powers.FullCompatibility.FunctionDropInverse (object c S 1) (object c S) (function c S data) (drop c S data l) l

/-- The original source-power/currying comparison preserves the complete original drop square. -/
def PowerFunctionDropCompatibility (S : ℕ → V) (data : Data c S) : Prop :=
  letI := OriginalSelectedPowerData.monoidalData c
  letI := OriginalSelectedPowerData.closedData c
  ∀ l : UnitArrowType c S,
    Powers.FullCompatibility.FunctionDrop (object c S 1) (object c S) (powerFunction c S data) (drop c S data l) l

/-- Both inverse source-power/currying maps retain every original source arrow and target object. -/
def PowerFunctionDropInverseCompatibility (S : ℕ → V) (data : Data c S) : Prop :=
  letI := OriginalSelectedPowerData.monoidalData c
  letI := OriginalSelectedPowerData.closedData c
  ∀ l : UnitArrowType c S,
    Powers.FullCompatibility.FunctionDropInverse (object c S 1) (object c S) (powerFunction c S data)
      (drop c S data l) l

/-- Forward naturality is stated on every complete original target arrow and every source degree. -/
def FunctionHomNaturality (S : ℕ → V) (data : Data c S) : Prop :=
  letI := OriginalSelectedPowerData.monoidalData c
  letI := OriginalSelectedPowerData.closedData c
  Powers.FullCompatibility.HomNaturality (object c S 1) (object c S) (function c S data)

/-- Inverse naturality is stated on the same full original target arrows and source degrees. -/
def FunctionInvNaturality (S : ℕ → V) (data : Data c S) : Prop :=
  letI := OriginalSelectedPowerData.monoidalData c
  letI := OriginalSelectedPowerData.closedData c
  Powers.FullCompatibility.InvNaturality (object c S 1) (object c S) (function c S data)

/-- Every complete direct-currying family equals the original source-power/currying family. -/
theorem functionFamilyEquality (S : ℕ → V) (data : Data c S) :
    FunctionFamilyEquality c S data := by
  let := OriginalSelectedPowerData.monoidalData c
  let := OriginalSelectedPowerData.closedData c
  funext n
  exact (Powers.FreeFamily.powerFunctionIso_eq
    (object c S 1) (object c S) data.zero data.successor n).symm

/-- Full source/E free-family data proves every original source-power drop square. -/
theorem powerDropCompatibility (S : ℕ → V) (data : Data c S) :
    PowerDropCompatibility c S data := by
  let := OriginalSelectedPowerData.monoidalData c
  intro l
  exact Powers.FullCompatibility.freePowerDrop (object c S 1) (object c S) data.zero data.successor l

/-- The complete inverse source-power square follows on the same actual original maps. -/
theorem powerDropInverseCompatibility (S : ℕ → V) (data : Data c S) :
    PowerDropInverseCompatibility c S data := by
  let := OriginalSelectedPowerData.monoidalData c
  intro l
  exact Powers.FullCompatibility.freePowerDropInverse (object c S 1) (object c S) data.zero data.successor l

/-- The original full generic free-family theorem proves every direct-currying source square. -/
theorem functionDropCompatibility (S : ℕ → V) (data : Data c S) :
    FunctionDropCompatibility c S data := by
  let := OriginalSelectedPowerData.monoidalData c
  let := OriginalSelectedPowerData.closedData c
  intro l
  exact Powers.FullCompatibility.freeFunctionDrop (object c S 1) (object c S) data.zero data.successor l

/-- The full original inverse generic square keeps the same transition and drop functions. -/
theorem functionDropInverseCompatibility (S : ℕ → V) (data : Data c S) :
    FunctionDropInverseCompatibility c S data := by
  let := OriginalSelectedPowerData.monoidalData c
  let := OriginalSelectedPowerData.closedData c
  intro l
  exact Powers.FullCompatibility.freeFunctionDropInverse (object c S 1) (object c S) data.zero data.successor l

/-- The equality of whole original function families retains every source-power square. -/
theorem powerFunctionDropCompatibility (S : ℕ → V) (data : Data c S) :
    PowerFunctionDropCompatibility c S data := by
  let := OriginalSelectedPowerData.monoidalData c
  let := OriginalSelectedPowerData.closedData c
  intro l
  exact Powers.FullCompatibility.freePowerFunctionDrop (object c S 1) (object c S) data.zero data.successor l

/-- The same whole-family equality retains every inverse source-power square. -/
theorem powerFunctionDropInverseCompatibility (S : ℕ → V) (data : Data c S) :
    PowerFunctionDropInverseCompatibility c S data := by
  let := OriginalSelectedPowerData.monoidalData c
  let := OriginalSelectedPowerData.closedData c
  intro l
  exact Powers.FullCompatibility.freePowerFunctionDropInverse (object c S 1) (object c S) data.zero data.successor l

/-- Every whole original function Iso supplies forward naturality in every degree and target arrow. -/
theorem functionHomNaturality (S : ℕ → V) (data : Data c S) :
    FunctionHomNaturality c S data := by
  let := OriginalSelectedPowerData.monoidalData c
  let := OriginalSelectedPowerData.closedData c
  exact Powers.FullCompatibility.homNaturality (object c S 1) (object c S) (function c S data)

/-- Both full inverse Iso maps preserve every original target arrow in every degree. -/
theorem functionInvNaturality (S : ℕ → V) (data : Data c S) :
    FunctionInvNaturality c S data := by
  let := OriginalSelectedPowerData.monoidalData c
  let := OriginalSelectedPowerData.closedData c
  exact Powers.FullCompatibility.invNaturality (object c S 1) (object c S) (function c S data)

end PointedCGWH.Spectra.Orthogonal.MMSSStabilization.FunctionIteration.TypedFullPowerData
end
end FullTypedSourcePowerCompatibility

section FullFreePairDataConstruction

noncomputable section
universe uPairDataV vPairDataV uPairDataJ
open CategoryTheory MonoidalCategory Limits
open CategoryTheory.EnrichedFunctorCat
open PointedCGWH.Spectra.NativeStableMonoidal
open scoped CategoryTheory.MonObj MonoidalClosed
attribute [local instance] Enriched.prodCategory MonoidalLeftAction.monoidalOppositeLeftAction
attribute [local instance] EnrichedDayKernel.ColimitMonoidal.smallestColimits

namespace PointedCGWH.Spectra.Orthogonal.MMSSStabilization.FunctionIteration.TypedFullPowerData

variable {V : Type uPairDataV} [Category.{vPairDataV} V] [MonoidalCategory V]
  [SymmetricCategory V] [MonoidalClosed V]
  [Category ℕ] [MonoidalCategory ℕ] [SymmetricCategory ℕ]
  [EnrichedOrdinaryCategory V ℕ] [HasColimitsOfSize.{0, 0} V]
  [HasProducts.{0} V] [HasEqualizers V]
  {q : Enriched.ModuleMappingR.SelectedSource V ℕ}
  {J : Type uPairDataJ} [EnrichedCategory V J]
  (c : CanonicalSourceFreeSmash.SelectedPair.Context q J)

/-- The original zero Iso and entire free-pair family construct the complete source-power data. -/
def ofFreePair (S : ℕ → V) (z : ZeroType c S)
    (coefficient : ∀ n, S (c.tensorIndex 1 n) ≅ S 1 ⊗ S n)
    (degree : ∀ n, c.tensorIndex 1 n = n + 1)
    (pair : OrthogonalSourcePair.SelectedBifunctor.FamilyType c) : Data c S := by
  let successor : ∀ n, FullSourceFreePair.SuccessorComponentType c S n :=
    FullSourceFreePair.successor c S coefficient degree pair
  exact { zero := z, successor := successor }

/-- Both original zero-source maps are the same complete input Iso. -/
theorem ofFreePair_zero (S : ℕ → V) (z : ZeroType c S)
    (coefficient : ∀ n, S (c.tensorIndex 1 n) ≅ S 1 ⊗ S n)
    (degree : ∀ n, c.tensorIndex 1 n = n + 1)
    (pair : OrthogonalSourcePair.SelectedBifunctor.FamilyType c) :
    (ofFreePair c S z coefficient degree pair).zero = z := rfl

/-- Every complete successor Iso is the original free-pair/coefficient/degree composition. -/
theorem ofFreePair_successor (S : ℕ → V) (z : ZeroType c S)
    (coefficient : ∀ n, S (c.tensorIndex 1 n) ≅ S 1 ⊗ S n)
    (degree : ∀ n, c.tensorIndex 1 n = n + 1)
    (pair : OrthogonalSourcePair.SelectedBifunctor.FamilyType c) :
    (ofFreePair c S z coefficient degree pair).successor =
      FullSourceFreePair.successor c S coefficient degree pair := rfl

end PointedCGWH.Spectra.Orthogonal.MMSSStabilization.FunctionIteration.TypedFullPowerData

end
end FullFreePairDataConstruction







end NativeFreePowerSource
end
