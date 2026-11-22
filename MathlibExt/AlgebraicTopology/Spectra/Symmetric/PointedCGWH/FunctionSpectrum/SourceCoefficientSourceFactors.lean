/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.Spectra.Symmetric.PointedCGWH.FunctionSpectrum.FreeSourceCoefficientBase
import MathlibExt.AlgebraicTopology.Spectra.Symmetric.PointedCGWH.FunctionSpectrum.FreeComparison
import MathlibExt.AlgebraicTopology.Spectra.Symmetric.PointedCGWH.FunctionSpectrum.FreeCoefficientSourceFunctor

/-!
# The complete original source factors of the native free-function comparison

The actual source equality, original module comparison and carrier counit
are retained as entire natural isomorphisms. These readbacks use the existing
comparison constructor and its original equality isomorphism.
-/

set_option autoImplicit false
noncomputable section
universe u v

open CategoryTheory MonoidalCategory Limits
open CategoryTheory.EnrichedFunctorCat
open scoped MonoidalClosed CategoryTheory.MonObj

namespace NativeOmegaRecovery.NativeSymmetricFreeFunction

private abbrev I := Operad.SmallFinBijGroupoid
private abbrev V := PointedCGWH.{u, v}
private abbrev A := PointedCGWH.sphereSequenceCommMon.{u, v}
private abbrev S := PointedCGWH.sphereSequence.{u, v}
private abbrev Carrier :=
  EnrichedFunctorCat V.{u, v} PointedCGWH.SymmetricOperatorIndex.{u, v}

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

open PointedCGWH.SymmetricModulePresentation

private theorem tripleIso_hom_app {C : Type*} {D : Type*}
    [Category C] [Category D] {F G H K : C ⥤ D}
    (e : F ≅ G) (e' : G ≅ H) (e'' : H ≅ K) (X : C) :
    (e ≪≫ e' ≪≫ e'').hom.app X =
      e.hom.app X ≫ e'.hom.app X ≫ e''.hom.app X := rfl

private theorem factorization_hom_app {C : Type*} {D : Type*}
    [Category C] [Category D] {F G H K : C ⥤ D}
    (c : F ≅ K) (e : F ≅ G) (e' : G ≅ H) (e'' : H ≅ K)
    (h : c = e ≪≫ e' ≪≫ e'') (X : C) :
    c.hom.app X = e.hom.app X ≫ e'.hom.app X ≫ e''.hom.app X :=
  (congrArg (fun q => q.hom.app X) h).trans (tripleIso_hom_app e e' e'' X)

private theorem originalSource_hom {C : Type*} [Category C]
    [MonoidalCategory C] [BraidedCategory C] [MonoidalClosed C]
    [HasCoequalizers C] [HasEqualizers C]
    (B : CommMon C) {D : Type*} [Category D] (E : Mod C B.X ≌ D)
    (N : Mod C B.X) (X : D) :
    (eqToIso (NativeOmegaPreparation.ModuleFunctionTransport.sourceFunctor_obj B E N)).hom.app X =
      𝟙 ((NativeOmegaPreparation.ModuleFunctionTransport.sourceFunctor B E).obj (.op N) |>.obj X) :=
  rfl

private theorem identity_component {W : Type*} [Category W] [MonoidalCategory W]
    [BraidedCategory W] [MonoidalClosed W]
    {J : Type*} [EnrichedCategory W J] (F : EnrichedFunctorCat W J)
    (p : F ⟶ F) (h : p = 𝟙 F) (a : J) :
    component p a = 𝟙 (F.toEnrichedFunctor.obj a) :=
  (congrArg (fun q => component q a) h).trans (component_id F a)

private theorem originalSource_hom_of_eq {C : Type*} [Category C]
    [MonoidalCategory C] [BraidedCategory C] [MonoidalClosed C]
    [HasCoequalizers C] [HasEqualizers C]
    (B : CommMon C) {D : Type*} [Category D] (E : Mod C B.X ≌ D)
    (N : Mod C B.X)
    (s : (NativeOmegaPreparation.ModuleFunctionTransport.sourceFunctor B E).obj (.op N) ≅
      E.inverse ⋙ Mod.internalHom B N ⋙ E.functor)
    (hs : s = eqToIso
      (NativeOmegaPreparation.ModuleFunctionTransport.sourceFunctor_obj B E N))
    (X : D) :
    s.hom.app X =
      𝟙 ((NativeOmegaPreparation.ModuleFunctionTransport.sourceFunctor B E).obj (.op N) |>.obj X) :=
  (congrArg (fun q => q.hom.app X) hs).trans (originalSource_hom B E N X)

private theorem originalSource_component_of_eq {C : Type*} [Category C]
    [MonoidalCategory C] [BraidedCategory C] [MonoidalClosed C]
    [HasCoequalizers C] [HasEqualizers C]
    (B : CommMon C) {W : Type*} [Category W] [MonoidalCategory W]
    [BraidedCategory W] [MonoidalClosed W] {J : Type*} [EnrichedCategory W J]
    (E : Mod C B.X ≌ EnrichedFunctorCat W J) (N : Mod C B.X)
    (s : (NativeOmegaPreparation.ModuleFunctionTransport.sourceFunctor B E).obj (.op N) ≅
      E.inverse ⋙ Mod.internalHom B N ⋙ E.functor)
    (hs : s = eqToIso
      (NativeOmegaPreparation.ModuleFunctionTransport.sourceFunctor_obj B E N))
    (X : EnrichedFunctorCat W J) (a : J) :
    component (s.hom.app X) a =
      𝟙 ((((NativeOmegaPreparation.ModuleFunctionTransport.sourceFunctor B E).obj
        (.op N)).obj X).toEnrichedFunctor.obj a) :=
  identity_component _ (s.hom.app X) (originalSource_hom_of_eq B E N s hs X) a

/-- The original full source transport is the equality isomorphism of the
actual module-function source equality. -/
def comparisonSourceTransport (r : I) (M : V.{u, v}) :
    NativeOmegaPreparation.SymmetricFunction.functor r M ≅
      operatorToModule ⋙ Mod.internalHom A.{u, v} ((Mod.dayFreeAt S.{u, v} r).obj M) ⋙
        moduleToOperator :=
  eqToIso (comparison_source r M)

/-- The complete equality-isomorphism factor used by the original comparison. -/
def comparisonSourceFactor (r : I) (M : V.{u, v}) := eqToIso (comparison_source r M)

/-- The original entire module comparison is whiskered by the inverse carrier. -/
def comparisonModuleFactor (r : I) (M : V.{u, v}) :=
  Functor.isoWhiskerLeft operatorToModule.{u, v} (moduleOperatorComparison r M)

/-- The original carrier counit is whiskered by the full shifted cotensor. -/
def comparisonRecoveryFactor (r : I) (M : V.{u, v}) :=
  Functor.isoWhiskerRight operatorRecoveryNatIso.{u, v}
    (PointedCGWH.SymmetricShift.functor.{u, v} r ⋙ cotensor M)

/-- The named source transport is the same entire original source factor. -/
theorem comparisonSourceTransport_eq_factor (r : I) (M : V.{u, v}) :
    comparisonSourceTransport r M = comparisonSourceFactor r M := rfl

/-- The full source transport retains the equality isomorphism appearing in
the unchanged original comparison constructor. -/
theorem comparisonSourceTransport_eq_old (r : I) (M : V.{u, v}) :
    comparisonSourceTransport r M =
      eqToIso (NativeOmegaPreparation.ModuleFunctionTransport.sourceFunctor_obj A.{u, v}
        moduleOperatorEquivalence.{u, v} ((Mod.dayFreeAt S.{u, v} r).obj M)) := rfl

/-- The existing comparison retains all three original natural-isomorphism
factors before any source input or component is selected. -/
theorem comparison_factorization (r : I) (M : V.{u, v}) :
    comparison r M =
      comparisonSourceFactor r M ≪≫ comparisonModuleFactor r M ≪≫
        comparisonRecoveryFactor r M := rfl

/-- Every original target input retains all three full forward components. -/
theorem comparison_hom_factors (r : I) (M : V.{u, v}) (X : Carrier.{u, v}) :
    type_of% (factorization_hom_app (comparison r M) (comparisonSourceFactor r M)
      (comparisonModuleFactor r M) (comparisonRecoveryFactor r M)
      (comparison_factorization r M) X) :=
  factorization_hom_app (comparison r M) (comparisonSourceFactor r M)
    (comparisonModuleFactor r M) (comparisonRecoveryFactor r M)
    (comparison_factorization r M) X

/-- The same complete forward word retains the original typed source transport. -/
theorem comparison_hom_transport_factors (r : I) (M : V.{u, v}) (X : Carrier.{u, v}) :
    type_of% (factorization_hom_app (comparison r M) (comparisonSourceTransport r M)
      (comparisonModuleFactor r M) (comparisonRecoveryFactor r M)
      (comparison_factorization r M) X) :=
  factorization_hom_app (comparison r M) (comparisonSourceTransport r M)
    (comparisonModuleFactor r M) (comparisonRecoveryFactor r M)
    (comparison_factorization r M) X

/-- The module factor uses the original entire comparison at the actual
inverse-carrier image of every native input. -/
theorem comparisonModuleFactor_hom_app_exact (r : I) (M : V.{u, v}) (X : Carrier.{u, v}) :
    (comparisonModuleFactor r M).hom.app X =
      (moduleOperatorComparison r M).hom.app (operatorToModule.obj X) := rfl

/-- The actual source equality is definitionally the same complete function
value, so its original equality-isomorphism component is the identity. -/
theorem comparisonSourceTransport_hom_whole (r : I) (M : V.{u, v}) (X : Carrier.{u, v}) :
    type_of% (originalSource_hom_of_eq A.{u, v} moduleOperatorEquivalence.{u, v}
      ((Mod.dayFreeAt S.{u, v} r).obj M) (comparisonSourceTransport r M)
      (comparisonSourceTransport_eq_old r M) X) :=
  originalSource_hom_of_eq A.{u, v} moduleOperatorEquivalence.{u, v}
    ((Mod.dayFreeAt S.{u, v} r).obj M) (comparisonSourceTransport r M)
    (comparisonSourceTransport_eq_old r M) X

/-- Every enriched output component retains that same original source identity. -/
theorem comparisonSourceTransport_hom_component
    (r : I) (M : V.{u, v}) (X : Carrier.{u, v}) (n : I) :
    type_of% (originalSource_component_of_eq A.{u, v} moduleOperatorEquivalence.{u, v}
      ((Mod.dayFreeAt S.{u, v} r).obj M) (comparisonSourceTransport r M)
      (comparisonSourceTransport_eq_old r M) X (PointedCGWH.symmetricOperatorObj.{u, v} n)) :=
  originalSource_component_of_eq A.{u, v} moduleOperatorEquivalence.{u, v}
    ((Mod.dayFreeAt S.{u, v} r).obj M) (comparisonSourceTransport r M)
    (comparisonSourceTransport_eq_old r M) X (PointedCGWH.symmetricOperatorObj.{u, v} n)

end NativeOmegaRecovery.NativeSymmetricFreeFunction


namespace NativeOmegaRecovery.OriginalCarrierZeroSourceUnit

universe uC vC uD vD
variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
  (E : C ≌ D) {F : C ⥤ C} {R : D ⥤ D}
  (e : F ≅ E.functor ⋙ R ⋙ E.inverse) (u : R ≅ 𝟭 D)

/-- The entire original free-function/unit comparison retains the genuine
module comparison, both carrier counits and the given full unit comparison. -/
def functionUnitIso : E.inverse ⋙ F ⋙ E.functor ≅ 𝟭 D :=
  Functor.isoWhiskerLeft E.inverse (FreeFunctionCarrierComparison.collapse E e) ≪≫
    Functor.isoWhiskerRight E.counitIso R ≪≫ u

/-- On an actual original module image the whole inverse unit prefix is the
genuine original free inverse preceded by the chosen unit/source maps. No
inverse-carrier object is reduced or replaced by the original object. -/
theorem functionUnitIso_inv_on_image (N : C) :
    (functionUnitIso E e u).inv.app (E.functor.obj N) =
      E.functor.map
        (E.unitIso.hom.app N ≫ E.inverse.map (u.inv.app (E.functor.obj N)) ≫
          e.inv.app N ≫ F.map (E.unitIso.hom.app N)) := by
  let X := E.functor.obj N
  let p : X ⟶ R.obj X := u.inv.app X
  let q : X ⟶ E.functor.obj (E.inverse.obj X) := E.counitIso.inv.app X
  let etaMap : N ⟶ E.inverse.obj X := E.unitIso.hom.app N
  have hEtaMap : E.functor.map etaMap = q := by
    apply (cancel_mono (E.counitIso.hom.app X)).mp
    change E.functor.map (E.unitIso.hom.app N) ≫
        E.counitIso.hom.app (E.functor.obj N) =
      E.counitIso.inv.app X ≫ E.counitIso.hom.app X
    rw [E.functor_unit_comp N]
    exact (E.counitIso.app X).inv_hom_id.symm
  have hOne := E.counitIso.inv.naturality (R.map q)
  have hTwo := E.counitIso.inv.naturality p
  have hFree := e.inv.naturality etaMap
  dsimp only [Functor.comp_map] at hOne hTwo hFree
  rw [hEtaMap] at hFree
  dsimp only [functionUnitIso, FreeFunctionCarrierComparison.collapse]
  simp only [Iso.trans_inv, NatTrans.comp_app, Functor.isoWhiskerLeft_inv,
    Functor.isoWhiskerRight_inv, Functor.whiskerLeft_app, Functor.whiskerRight_app]
  simp only [Category.assoc]
  change p ≫ R.map q ≫ E.counitIso.inv.app (R.obj (E.functor.obj (E.inverse.obj X))) ≫
      E.functor.map (e.inv.app (E.inverse.obj X)) =
    E.functor.map (etaMap ≫ E.inverse.map p ≫ e.inv.app N ≫ F.map etaMap)
  calc
    _ = p ≫ E.counitIso.inv.app (R.obj X) ≫
        E.functor.map (E.inverse.map (R.map q)) ≫
          E.functor.map (e.inv.app (E.inverse.obj X)) := by
      rw [reassoc_of% hOne]
    _ = q ≫ E.functor.map (E.inverse.map p) ≫
        E.functor.map (E.inverse.map (R.map q)) ≫
          E.functor.map (e.inv.app (E.inverse.obj X)) := by
      rw [reassoc_of% hTwo]
    _ = E.functor.map etaMap ≫ E.functor.map (E.inverse.map p) ≫
        E.functor.map (E.inverse.map (R.map q) ≫ e.inv.app (E.inverse.obj X)) := by
      rw [hEtaMap, E.functor.map_comp]
    _ = E.functor.map etaMap ≫ E.functor.map (E.inverse.map p) ≫
        E.functor.map (e.inv.app N ≫ F.map etaMap) := by
      rw [hFree]
    _ = _ := by simp only [Functor.map_comp]

/-- A genuine equality of the complete original chosen unit comparison is
eliminated before taking its inverse on any actual original module image. -/
theorem functionUnitIso_inv_on_image_of_value
    (w : E.inverse ⋙ F ⋙ E.functor ≅ 𝟭 D)
    (hw : w = functionUnitIso E e u) (N : C) :
    w.inv.app (E.functor.obj N) =
      E.functor.map
        (E.unitIso.hom.app N ≫ E.inverse.map (u.inv.app (E.functor.obj N)) ≫
          e.inv.app N ≫ F.map (E.unitIso.hom.app N)) := by
  cases hw
  exact functionUnitIso_inv_on_image E e u N

end NativeOmegaRecovery.OriginalCarrierZeroSourceUnit

namespace NativeOmegaRecovery.OriginalCarrierZeroSourceUnit

universe uC vC uD vD
variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
  (E : C ≌ D) {F : C ⥤ C} {S R : D ⥤ D}
  (s : S ≅ E.inverse ⋙ F ⋙ E.functor)
  (e : F ≅ E.functor ⋙ R ⋙ E.inverse) (u : R ≅ 𝟭 D)

/-- The complete original source comparison precedes the entire carrier-unit
comparison. -/
def sourceFunctionUnitIso : S ≅ 𝟭 D := s ≪≫ functionUnitIso E e u

/-- The source inverse remains after the same complete module inverse word. -/
theorem sourceFunctionUnitIso_inv_on_image (N : C) :
    (sourceFunctionUnitIso E s e u).inv.app (E.functor.obj N) =
      E.functor.map
        (E.unitIso.hom.app N ≫ E.inverse.map (u.inv.app (E.functor.obj N)) ≫
          e.inv.app N ≫ F.map (E.unitIso.hom.app N)) ≫
        s.inv.app (E.functor.obj N) := by
  change (functionUnitIso E e u).inv.app (E.functor.obj N) ≫
    s.inv.app (E.functor.obj N) = _
  rw [functionUnitIso_inv_on_image]

end NativeOmegaRecovery.OriginalCarrierZeroSourceUnit


namespace NativeOmegaRecovery.NativeSymmetricSourceMatch

private abbrev I := Operad.SmallFinBijGroupoid
private abbrev V := PointedCGWH.{u, v}
private abbrev S := PointedCGWH.sphereSequence.{u, v}
private abbrev A := PointedCGWH.sphereSequenceCommMon.{u, v}

attribute [local instance] Operad.SmallFinBijGroupoid.instMonoidalCategory
  Operad.SmallFinBijGroupoid.instSymmetricCategory
  PointedCGWH.copowerUnderlyingEnrichedOrdinary PointedCGWH.copowerUnderlyingMonoidal
  PointedCGWH.sphereSequenceMonObj PointedCGWH.sphereSequenceIsCommMonObj
  PointedCGWH.EnrichedMapping.hasSmallLimits
  NativeOmegaPreparation.SymmetricFunction.sequenceCoequalizers
  NativeOmegaPreparation.SymmetricFunction.sequenceEqualizers
  NativeOmegaPreparation.SymmetricFunction.sequenceClosed
  PointedCGWH.SymmetricFunctionFactories.indexedCoproducts
  PointedCGWH.SymmetricFunctionFactories.tensorExtensions
  PointedCGWH.SymmetricFunctionFactories.unitExtensions
  PointedCGWH.SymmetricFunctionFactories.tensorLeftTensorShape
  PointedCGWH.SymmetricFunctionFactories.tensorRightTensorShape
  PointedCGWH.SymmetricFunctionFactories.tensorLeftUnitShape
  PointedCGWH.SymmetricFunctionFactories.tensorRightUnitShape
  PointedCGWH.SymmetricFunctionFactories.tensorRightMixedUnitShape
  PointedCGWH.SymmetricFunctionFactories.tensorRightTripleShape
  PointedCGWH.SymmetricFunctionFactories.internalHomEnds
  PointedCGWH.originalSymmetricSequenceMonoidal
  PointedCGWH.originalSymmetricSequenceBraided PointedCGWH.originalSymmetricSequenceSymmetric

open PointedCGWH.SymmetricModulePresentation
open NativeSymmetricFreeFunction

/-- The actual sphere Day free functor at the given original finite index. -/
def chosenFreeFunctor (r : I) := Mod.dayFreeAt S.{u, v} r

/-- The same complete free functor retains the original evaluation adjoint and Day presentation. -/
def freeFunctorRecipe (r : I) :=
  (evaluationLeftAdjoint V.{u, v} r ⋙ (DayFunctor.equiv I V.{u, v}).symm.functor) ⋙
    Mod.free S.{u, v}

/-- The whole chosen free functor is its original evaluation-adjoint recipe. -/
theorem chosenFreeFunctor_eq_recipe (r : I) :
    chosenFreeFunctor.{u, v} r = freeFunctorRecipe.{u, v} r := rfl

/-- The full original internal-Hom functor out of the chosen free module. -/
def chosenHomSource (r : I) (M : V.{u, v}) :=
  Mod.internalHom A.{u, v} ((chosenFreeFunctor.{u, v} r).obj M)

/-- The complete internal-Hom source retains the original sequence and free-module constructors. -/
def homSourceRecipe (r : I) (M : V.{u, v}) :=
  Mod.internalHom A.{u, v} ((Mod.free S.{u, v}).obj
    (.mk ((evaluationLeftAdjoint V.{u, v} r).obj M)))

/-- All target objects and maps of the chosen Hom source have the original constructor. -/
theorem chosenHomSource_eq_recipe (r : I) (M : V.{u, v}) :
    chosenHomSource.{u, v} r M = homSourceRecipe.{u, v} r M := by
  unfold chosenHomSource
  rw [chosenFreeFunctor_eq_recipe]
  rfl

/-- The whole coefficient pre-map source is the same original free-module Hom functor. -/
theorem coefficientSource_eq_recipe (r : I) (M : V.{u, v}) :
    NativeScalarCoefficient.coefficientComparisonSourceFunctor.{u, v} r M =
      homSourceRecipe.{u, v} r M := by
  unfold NativeScalarCoefficient.coefficientComparisonSourceFunctor homSourceRecipe
  rw [NativeScalarCoefficient.coefficientFreeFunctor_eq_original]
  rfl

/-- The actual source read from the original module comparison has that full Hom recipe. -/
theorem actualSource_eq_recipe (r : I) (M : V.{u, v}) :
    NativeScalarCoefficient.originalComparisonSourceFunctor.{u, v} r M =
      homSourceRecipe.{u, v} r M :=
  (NativeScalarCoefficient.originalComparisonSourceFunctor_eq_coefficient.{u, v} r M).trans
    (coefficientSource_eq_recipe.{u, v} r M)

/-- The complete native source retains both original carrier functors and the chosen module Hom. -/
theorem nativeSource_eq_chosenHom (r : I) (M : V.{u, v}) :
    NativeOmegaPreparation.SymmetricFunction.functor.{u, v} r M =
      moduleOperatorEquivalence.{u, v}.inverse ⋙ chosenHomSource.{u, v} r M ⋙
        moduleOperatorEquivalence.{u, v}.functor :=
  comparison_source.{u, v} r M

/-- The whole native source has the original evaluation/free-module Hom recipe. -/
theorem nativeSource_eq_recipe (r : I) (M : V.{u, v}) :
    NativeOmegaPreparation.SymmetricFunction.functor.{u, v} r M =
      moduleOperatorEquivalence.{u, v}.inverse ⋙ homSourceRecipe.{u, v} r M ⋙
        moduleOperatorEquivalence.{u, v}.functor :=
  (nativeSource_eq_chosenHom.{u, v} r M).trans
    (congrArg (fun F => moduleOperatorEquivalence.{u, v}.inverse ⋙ F ⋙
      moduleOperatorEquivalence.{u, v}.functor) (chosenHomSource_eq_recipe.{u, v} r M))

/-- Every index and coefficient retain the actual entire source of the original module
comparison. -/
theorem nativeSource_eq_actualComparisonSource (r : I) (M : V.{u, v}) :
    NativeOmegaPreparation.SymmetricFunction.functor.{u, v} r M =
      moduleOperatorEquivalence.{u, v}.inverse ⋙
        NativeScalarCoefficient.originalComparisonSourceFunctor.{u, v} r M ⋙
          moduleOperatorEquivalence.{u, v}.functor :=
  (nativeSource_eq_recipe.{u, v} r M).trans
    (congrArg (fun F => moduleOperatorEquivalence.{u, v}.inverse ⋙ F ⋙
      moduleOperatorEquivalence.{u, v}.functor) (actualSource_eq_recipe.{u, v} r M).symm)

/-- The proved whole source equality supplies its original equality isomorphism. -/
def actualSourceTransport (r : I) (M : V.{u, v}) :=
  eqToIso (nativeSource_eq_actualComparisonSource.{u, v} r M)

private theorem eqToIso_same_source_heq {C : Type*} [Category C]
    {X Y Z : C} (h : X = Y) (h' : X = Z) : HEq (eqToIso h) (eqToIso h') := by
  cases h
  cases h'
  rfl

/-- The existing entire source transport is the same equality isomorphism over the actual source. -/
theorem sourceTransport_heq_actualSource (r : I) (M : V.{u, v}) :
    HEq (comparisonSourceTransport.{u, v} r M) (actualSourceTransport.{u, v} r M) :=
  eqToIso_same_source_heq (comparison_source.{u, v} r M)
    (nativeSource_eq_actualComparisonSource.{u, v} r M)

end NativeOmegaRecovery.NativeSymmetricSourceMatch


namespace NativeOmegaRecovery.OriginalCarrierZeroSourceUnit

universe uC vC uD vD
variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
  (E : C ≌ D) {F : C ⥤ C} {S R : D ⥤ D}
  (s : S ≅ E.inverse ⋙ F ⋙ E.functor)
  (e : F ≅ E.functor ⋙ R ⋙ E.inverse) (u : R ≅ 𝟭 D)

/-- A proved whole source factorization carries the given entire unit comparison through the
original module comparison. -/
theorem source_unit_of_factorization (w : S ≅ R)
    (h : w = s ≪≫ Functor.isoWhiskerLeft E.inverse
      (FreeFunctionCarrierComparison.collapse E e) ≪≫
        Functor.isoWhiskerRight E.counitIso R) :
    w ≪≫ u = sourceFunctionUnitIso E s e u := by
  rw [h]
  simp only [sourceFunctionUnitIso, functionUnitIso, Iso.trans_assoc]

/-- Equality of whole unit comparisons is eliminated before the inverse is read on any original
module image. -/
theorem source_unit_inv_on_image_of_value (w : S ≅ 𝟭 D)
    (hw : w = sourceFunctionUnitIso E s e u) (N : C) :
    w.inv.app (E.functor.obj N) =
      E.functor.map
        (E.unitIso.hom.app N ≫ E.inverse.map (u.inv.app (E.functor.obj N)) ≫
          e.inv.app N ≫ F.map (E.unitIso.hom.app N)) ≫
        s.inv.app (E.functor.obj N) := by
  rw [hw]
  exact sourceFunctionUnitIso_inv_on_image E s e u N

end NativeOmegaRecovery.OriginalCarrierZeroSourceUnit

namespace NativeOmegaRecovery.SourceEquality

universe uC vC
variable {C : Type uC} [Category.{vC} C] {S G G' R : C}

/-- Two whole source equalities and one full tail identity give the same composite isomorphism. -/
theorem eqToIso_comp_eq_of_heq (h : S = G) (h' : S = G')
    (k : G ≅ R) (k' : G' ≅ R) (hk : HEq k k') :
    eqToIso h ≪≫ k = eqToIso h' ≪≫ k' := by
  cases h
  cases h'
  simpa only [eqToIso_refl, Iso.refl_trans] using eq_of_heq hk

end NativeOmegaRecovery.SourceEquality

namespace NativeOmegaRecovery.OriginalCarrierZeroSourceUnit

universe uC vC uD vD
variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]

/-- The entire source comparison precedes the original module and carrier-unit comparison. -/
def sourceUnitFromModule (E : C ≌ D) {F : C ⥤ C} {R : D ⥤ D}
    (e : F ≅ E.functor ⋙ R ⋙ E.inverse) (u : R ≅ 𝟭 D)
    {S : D ⥤ D} (s : S ≅ E.inverse ⋙ F ⋙ E.functor) : S ≅ 𝟭 D :=
  sourceFunctionUnitIso E s e u

end NativeOmegaRecovery.OriginalCarrierZeroSourceUnit

namespace NativeOmegaRecovery.NativeSymmetricFreeFunction

attribute [local instance] Operad.SmallFinBijGroupoid.instMonoidalCategory
  Operad.SmallFinBijGroupoid.instSymmetricCategory
  PointedCGWH.copowerUnderlyingEnrichedOrdinary PointedCGWH.copowerUnderlyingMonoidal
  PointedCGWH.sphereSequenceMonObj PointedCGWH.sphereSequenceIsCommMonObj
  PointedCGWH.EnrichedMapping.hasSmallLimits
  NativeOmegaPreparation.SymmetricFunction.sequenceCoequalizers
  NativeOmegaPreparation.SymmetricFunction.sequenceEqualizers
  NativeOmegaPreparation.SymmetricFunction.sequenceClosed
  PointedCGWH.SymmetricFunctionFactories.indexedCoproducts
  PointedCGWH.SymmetricFunctionFactories.tensorExtensions
  PointedCGWH.SymmetricFunctionFactories.unitExtensions
  PointedCGWH.SymmetricFunctionFactories.tensorLeftTensorShape
  PointedCGWH.SymmetricFunctionFactories.tensorRightTensorShape
  PointedCGWH.SymmetricFunctionFactories.tensorLeftUnitShape
  PointedCGWH.SymmetricFunctionFactories.tensorRightUnitShape
  PointedCGWH.SymmetricFunctionFactories.tensorRightMixedUnitShape
  PointedCGWH.SymmetricFunctionFactories.tensorRightTripleShape
  PointedCGWH.SymmetricFunctionFactories.internalHomEnds
  PointedCGWH.originalSymmetricSequenceMonoidal
  PointedCGWH.originalSymmetricSequenceBraided PointedCGWH.originalSymmetricSequenceSymmetric

open PointedCGWH.SymmetricModulePresentation
open OriginalCarrierZeroSourceUnit
open NativeSymmetricSourceMatch

/-- The actual source comparison uses the same original module NatIso and
carrier counit, before its unit map is selected. -/
def comparisonSourceUnit (r : I) (M : V.{u, v})
    (uR : PointedCGWH.SymmetricShift.functor.{u, v} r ⋙ cotensor M ≅ 𝟭 Carrier.{u, v}) :=
  sourceUnitFromModule moduleOperatorEquivalence.{u, v} (moduleComparisonNat r M) uR
    (actualSourceTransport r M)


end NativeOmegaRecovery.NativeSymmetricFreeFunction
