/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.SymmetricSmashHomotopyExtension.FunctionScalarCoefficient
import MathlibExt.CategoryTheory.Adjunction.ParametrizedLeftIsoComparison
import Mathlib.CategoryTheory.EqToHom
import Mathlib.CategoryTheory.Adjunction.Parametrized

/-!
# Scalar smash and function-spectrum bifunctors

Compares the complete transported smash bifunctor with the native function-spectrum bifunctor
and its parametrized adjunction. The formulas retain source maps and the full family of
fixed-source adjunctions.
-/

set_option autoImplicit false
noncomputable section

universe u v uC vC uD vD uP vP uB vB

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open CategoryTheory.EnrichedFunctorCat
open scoped MonoidalCategory MonoidalClosed CategoryTheory.MonObj

universe uRetP vRetP uRetB vRetB uRetD vRetD

private def retainParametrizedFamily {P : Type uRetP} [Category.{vRetP} P]
    {B : Type uRetB} [Category.{vRetB} B] {D : Type uRetD} [Category.{vRetD} D]
    {F F' : P ⥤ B ⥤ D} {G G' : Pᵒᵖ ⥤ D ⥤ B}
    (a : F ⊣₂ G) (hF : F = F') (hG : G = G')
    (adj : ∀ X, F'.obj X ⊣ G'.obj (.op X)) (hAdj : HEq a.adj adj) : F' ⊣₂ G' :=
  ParametrizedAdjunction.mk' adj (by
    cases hF
    cases hG
    have ha : a.adj = adj := eq_of_heq hAdj
    cases ha
    intro X Y p Z W f
    exact a.homEquiv_naturality_one p f)

universe uCopyA vCopyA uCopyD vCopyD

private theorem copyObject_eq {A : Type uCopyA} [Category.{vCopyA} A]
    {D : Type uCopyD} [Category.{vCopyD} D] (F : A ⥤ D) (o : A → D) (h : F.obj = o) :
    F.copyObj o (fun X => eqToIso (congrFun h X)) = F := by
  cases h
  exact CategoryTheory.Functor.ext_of_iso
    (F.isoCopyObj F.obj (fun X => eqToIso (congrFun (rfl : F.obj = F.obj) X))).symm
    (fun _ => rfl) (fun _ => rfl)

namespace PointedCGWH.Spectra.NativeStableMonoidal.SymmetricScalarSmash.CoefficientPrimitive

private theorem functor_eta {C : Type uC} [Category.{vC} C]
    {D : Type uD} [Category.{vD} D] (F : C ⥤ D) :
    ({ obj := F.obj, map := F.map, map_id := F.map_id, map_comp := F.map_comp } : C ⥤ D) =
      F := rfl

private theorem wholeFunctorMap_heq {C : Type uC} [Category.{vC} C]
    {D : Type uD} [Category.{vD} D] {F G : C ⥤ D} (h : F = G)
    {X Y : C} (f : X ⟶ Y) : HEq (F.map f) (G.map f) := by
  cases h
  exact HEq.refl _

private theorem smashBifunctor_getter {C : Type uC} [Category.{vC} C]
    [MonoidalCategory C] [BraidedCategory C] [MonoidalClosed C]
    [HasCoequalizers C] (A : CommMon C)
    {D : Type uD} [Category.{vD} D] (E : Mod C A.X ≌ D) :
    (Mod.EquivalenceFunctionTransport.smashBifunctor A E).obj =
      Mod.EquivalenceFunctionTransport.smashFunctor A E := rfl






end PointedCGWH.Spectra.NativeStableMonoidal.SymmetricScalarSmash.CoefficientPrimitive

namespace PointedCGWH.Spectra.NativeStableMonoidal.SymmetricScalarSmash

private abbrev I := Operad.SmallFinBijGroupoid
private abbrev V := PointedCGWH.{u, v}
private abbrev A := PointedCGWH.sphereSequenceCommMon.{u, v}
private abbrev E := PointedCGWH.SymmetricModulePresentation.moduleOperatorEquivalence.{u, v}

attribute [local instance] Operad.SmallFinBijGroupoid.instMonoidalCategory
  Operad.SmallFinBijGroupoid.instSymmetricCategory
  PointedCGWH.copowerUnderlyingEnrichedOrdinary PointedCGWH.copowerUnderlyingMonoidal
  PointedCGWH.sphereSequenceMonObj PointedCGWH.sphereSequenceIsCommMonObj
  PointedCGWH.EnrichedMapping.hasSmallLimits
  NativeOmegaPreparation.SymmetricFunction.sequenceCoequalizers
  NativeOmegaPreparation.SymmetricFunction.sequenceEqualizers
  NativeOmegaPreparation.SymmetricFunction.sequenceClosed
  PointedCGWH.originalSymmetricSequenceMonoidal
  PointedCGWH.originalSymmetricSequenceBraided PointedCGWH.originalSymmetricSequenceSymmetric

private theorem nativeWholeRight :
    Mod.EquivalenceFunctionTransport.bifunctor A.{u, v} E.{u, v} =
      NativeOmegaPreparation.NativeSymmetricFunction.bifunctor.{u, v} := rfl

private def zeroFreeFunctor : V.{u, v} ⥤ Carrier.{u, v} where
  obj := zeroFree
  map := Free.coefficientMap (PointedCGWH.symmetricOperatorObj (𝟙_ I))
  map_id := (Free.functor (PointedCGWH.symmetricOperatorObj (𝟙_ I))).map_id
  map_comp := (Free.functor (PointedCGWH.symmetricOperatorObj (𝟙_ I))).map_comp

private theorem zeroFreeFunctor_whole :
    zeroFreeFunctor.{u, v} = Free.functor (PointedCGWH.symmetricOperatorObj (𝟙_ I)) := rfl

private def nativeRightBifunctor : Carrier.{u, v}ᵒᵖ ⥤ Carrier.{u, v} ⥤ Carrier.{u, v} where
  obj := fun X => NativeOmegaPreparation.NativeSymmetricFunction.functor X.unop
  map := fun p => NativeOmegaPreparation.NativeSymmetricFunction.precompose p.unop
  map_id := NativeOmegaPreparation.NativeSymmetricFunction.bifunctor.map_id
  map_comp := NativeOmegaPreparation.NativeSymmetricFunction.bifunctor.map_comp

private theorem nativeRightBifunctor_whole :
    nativeRightBifunctor.{u, v} =
      NativeOmegaPreparation.NativeSymmetricFunction.bifunctor.{u, v} := by
  have h : nativeRightBifunctor.{u, v} =
      { obj := NativeOmegaPreparation.NativeSymmetricFunction.bifunctor.obj
        map := NativeOmegaPreparation.NativeSymmetricFunction.bifunctor.map
        map_id := NativeOmegaPreparation.NativeSymmetricFunction.bifunctor.map_id
        map_comp := NativeOmegaPreparation.NativeSymmetricFunction.bifunctor.map_comp } := rfl
  exact h.trans (CoefficientPrimitive.functor_eta _)

private theorem nativeWholeSmashGetter :
    Mod.EquivalenceFunctionTransport.smashFunctor A.{u, v} E.{u, v} =
      NativeOmegaPreparation.NativeSymmetricFunction.smashFunctor.{u, v} := rfl


private def nativeLeftBifunctor : Carrier.{u, v} ⥤ Carrier.{u, v} ⥤ Carrier.{u, v} :=
  (Mod.EquivalenceFunctionTransport.smashBifunctor A.{u, v} E.{u, v}).copyObj
    NativeOmegaPreparation.NativeSymmetricFunction.smashFunctor.{u, v}
    (fun X => eqToIso (congrFun
      ((CoefficientPrimitive.smashBifunctor_getter A.{u, v} E.{u, v}).trans nativeWholeSmashGetter) X))

private theorem nativeLeftBifunctor_whole :
    nativeLeftBifunctor.{u, v} =
      Mod.EquivalenceFunctionTransport.smashBifunctor A.{u, v} E.{u, v} :=
  copyObject_eq (Mod.EquivalenceFunctionTransport.smashBifunctor A.{u, v} E.{u, v})
    NativeOmegaPreparation.NativeSymmetricFunction.smashFunctor.{u, v}
    ((CoefficientPrimitive.smashBifunctor_getter A.{u, v} E.{u, v}).trans nativeWholeSmashGetter)

private theorem nativeWholeAdjunction :
    HEq (Mod.EquivalenceFunctionTransport.parametrizedAdjunction A.{u, v} E.{u, v}).adj
      NativeOmegaPreparation.NativeSymmetricFunction.adjunction.{u, v} := HEq.refl _

attribute [local irreducible] NativeOmegaPreparation.NativeSymmetricFunction.functor
  NativeOmegaPreparation.NativeSymmetricFunction.smashFunctor
  NativeOmegaPreparation.NativeSymmetricFunction.adjunction

private def nativeAdjunctionInitializer :
    ∀ X : Carrier.{u, v}, nativeLeftBifunctor.obj X ⊣ nativeRightBifunctor.obj (.op X) :=
  NativeOmegaPreparation.NativeSymmetricFunction.adjunction

private theorem nativeAdjunctionInitializer_whole :
    HEq nativeAdjunctionInitializer.{u, v}
      NativeOmegaPreparation.NativeSymmetricFunction.adjunction.{u, v} := HEq.refl _

private def nativeParametrized : nativeLeftBifunctor.{u, v} ⊣₂ nativeRightBifunctor.{u, v} :=
  retainParametrizedFamily
    (Mod.EquivalenceFunctionTransport.parametrizedAdjunction A.{u, v} E.{u, v})
    nativeLeftBifunctor_whole.symm
    (nativeWholeRight.trans nativeRightBifunctor_whole.symm)
    nativeAdjunctionInitializer nativeWholeAdjunction

private theorem nativeParametrized_adj (X : Carrier.{u, v}) :
    nativeParametrized.adj X = nativeAdjunctionInitializer X := rfl

attribute [local irreducible] zeroFree NativeOmegaPreparation.NativeSymmetricFunction.precompose

private def nativeScalarRight : V.{u, v}ᵒᵖ ⥤ Carrier.{u, v} ⥤ Carrier.{u, v} where
  obj := fun T => NativeOmegaPreparation.NativeSymmetricFunction.functor (zeroFree T.unop)
  map := fun p => NativeOmegaPreparation.NativeSymmetricFunction.precompose
    (zeroFreeFunctor.map p.unop)
  map_id := (zeroFreeFunctor.op ⋙ nativeRightBifunctor).map_id
  map_comp := (zeroFreeFunctor.op ⋙ nativeRightBifunctor).map_comp

private theorem nativeScalarRight_whole :
    nativeScalarRight.{u, v} = zeroFreeFunctor.op ⋙
      NativeOmegaPreparation.NativeSymmetricFunction.bifunctor.{u, v} := by
  rw [← nativeRightBifunctor_whole]
  rfl

attribute [local semireducible] zeroFree

set_option maxHeartbeats 500000 in
-- Keep the exact previously diagnosed right component constructor finite.
private def scalarRightComparison :
    nativeScalarRight.{u, v} ≅
      ScalarLeibniz.cotensorBifunctor (A := PointedCGWH.SymmetricOperatorIndex.{u, v}) :=
  NatIso.ofComponents (fun T => functionScalarIso T.unop) (by
    intro T T' p
    exact functionScalarIso_coefficient p.unop)

private theorem scalarRightComparison_app (T : V.{u, v}ᵒᵖ) :
    scalarRightComparison.app T = functionScalarIso T.unop := rfl














/-- The full original native balanced-smash bifunctor, with its original object getter retained. -/
def nativeSmashBifunctorBoundary : Carrier.{u, v} ⥤ Carrier.{u, v} ⥤ Carrier.{u, v} :=
  nativeLeftBifunctor

/-- The native smash constructor retains the entire original transported balanced-smash bifunctor. -/
theorem nativeSmashBifunctorBoundary_whole :
    nativeSmashBifunctorBoundary.{u, v} =
      Mod.EquivalenceFunctionTransport.smashBifunctor A.{u, v} E.{u, v} :=
  nativeLeftBifunctor_whole

set_option maxHeartbeats 500000 in
-- The original whole source-map specialization exceeded200k in kernel conversion.
/-- Every actual source map retains the complete original balanced source-smash map. -/
theorem nativeSmashBifunctorBoundary_map_heq {X Y : Carrier.{u, v}} (f : X ⟶ Y) :
    HEq (nativeSmashBifunctorBoundary.map f)
      (Mod.EquivalenceFunctionTransport.sourceSmashMap A.{u, v} E.{u, v} f) :=
  CoefficientPrimitive.wholeFunctorMap_heq
    (F := nativeSmashBifunctorBoundary)
    (G := Mod.EquivalenceFunctionTransport.smashBifunctor A.{u, v} E.{u, v})
    nativeSmashBifunctorBoundary_whole f

/-- The full original native function bifunctor, with its original object and map getters retained. -/
def nativeFunctionBifunctorBoundary : Carrier.{u, v}ᵒᵖ ⥤ Carrier.{u, v} ⥤ Carrier.{u, v} :=
  nativeRightBifunctor

/-- The entire native right constructor is the original native function bifunctor. -/
theorem nativeFunctionBifunctorBoundary_whole :
    nativeFunctionBifunctorBoundary.{u, v} =
      NativeOmegaPreparation.NativeSymmetricFunction.bifunctor.{u, v} :=
  nativeRightBifunctor_whole

/-- The complete original balanced adjunction is natural in the actual native source. -/
def retainedNativeParametrized :
    nativeSmashBifunctorBoundary.{u, v} ⊣₂ nativeFunctionBifunctorBoundary.{u, v} :=
  nativeParametrized

/-- The entire original adjunction initializer, typed over both complete native bifunctors. -/
def originalNativeAdjunctionFamily :
    ∀ X : Carrier.{u, v},
      nativeSmashBifunctorBoundary.obj X ⊣ nativeFunctionBifunctorBoundary.obj (.op X) :=
  nativeAdjunctionInitializer

/-- The typed family retains the exact original native adjunction constructor before any source object. -/
theorem originalNativeAdjunctionFamily_whole :
    HEq originalNativeAdjunctionFamily.{u, v}
      NativeOmegaPreparation.NativeSymmetricFunction.adjunction.{u, v} :=
  nativeAdjunctionInitializer_whole

/-- Each actual native component remains the exact original adjunction initializer. -/
theorem retainedNativeParametrized_adj (X : Carrier.{u, v}) :
    retainedNativeParametrized.adj X = originalNativeAdjunctionFamily X := rfl









end PointedCGWH.Spectra.NativeStableMonoidal.SymmetricScalarSmash
