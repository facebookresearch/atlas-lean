/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.Spectra.Symmetric.PointedCGWH.FunctionSpectrum.SourceCoefficientSourceGEN

/-!
# Original whole free-source and adjunction data

The original complete free objects are retained through the genuine original
coefficient object and monoid equalities before any source map or original
internal-Hom comparison is projected. The same original source functor, source
map and free-adjunction scalar generator are retained before native joins.
-/

set_option autoImplicit false
noncomputable section
universe u v
open CategoryTheory MonoidalCategory Limits
open CategoryTheory.EnrichedFunctorCat
open scoped MonoidalClosed CategoryTheory.MonObj

universe uC vC uJ vJ uW vW

private theorem free_object_of_original_data
    {C : Type uC} [Category.{vC} C] [MonoidalCategory C]
    (R R' : C) (m : MonObj R) (m' : MonObj R')
    (hR : R = R') (hm : HEq m m') (P : C) :
    HEq (letI : MonObj R := m; (Mod.free R).obj P)
      (letI : MonObj R' := m'; (Mod.free R').obj P) := by
  cases hR
  cases hm
  rfl

private theorem day_free_object_original
    {J : Type uJ} [Category.{vJ} J] [MonoidalCategory J]
    {W : Type uW} [Category.{vW} W] [MonoidalCategory W]
    [MonoidalCategory (DayFunctor J W)] (R : DayFunctor J W) [MonObj R]
    [∀ a b : J, HasCoproductsOfShape (a ⟶ b) W] (r : J) (K : W) :
    (Mod.dayFreeAt R r).obj K =
      (Mod.free R).obj (.mk ((evaluationLeftAdjoint W r).obj K)) := rfl

namespace NativeOmegaRecovery.NativeSymmetricSourceGEN.FreeSourceObjects
private abbrev I := Operad.SmallFinBijGroupoid
private abbrev V := PointedCGWH.{u, v}
private abbrev A := PointedCGWH.sphereSequenceCommMon.{u, v}
private abbrev S := PointedCGWH.sphereSequence.{u, v}

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

open PointedCGWH.SymmetricModulePresentation
open NativeSymmetricFreeFunction

/-- The whole actual Day free object retains the original free/evaluation
composite before its module data or any output is projected. -/
theorem actual_free_module_eq_original (r : I) (K : V.{u, v}) :
    NativeSymmetricFreeSource.freeModule.{u, v} r K =
      (Mod.free S.{u, v}).obj (.mk ((evaluationLeftAdjoint V.{u, v} r).obj K)) :=
  day_free_object_original S.{u, v} r K

/-- Every actual whole free module retains the canonical coefficient value
through the genuine original object and monoid data equalities. -/
theorem actual_free_module_heq_canonical (r : I) (K : V.{u, v}) :
    HEq (NativeSymmetricFreeSource.freeModule.{u, v} r K)
      (letI : MonObj A.{u, v}.X := A.{u, v}.mon;
        (Mod.free A.{u, v}.X).obj
          (.mk ((evaluationLeftAdjoint V.{u, v} r).obj K))) := by
  have hOriginal := actual_free_module_eq_original r K
  have hCanonical := free_object_of_original_data A.{u, v}.X S.{u, v}
    A.{u, v}.mon PointedCGWH.sphereSequenceMonObj.{u, v}
    NativeScalarCoefficient.sphereCoefficient_obj_eq.{u, v}
    (heq_of_eq NativeScalarCoefficient.sphereCoefficient_mon_eq.{u, v})
    (.mk ((evaluationLeftAdjoint V.{u, v} r).obj K))
  exact (heq_of_eq hOriginal).trans hCanonical.symm

/-- The actual entire free object equality is obtained before any source
arrow or original internal-Hom comparison is formed. -/
theorem actual_free_module_eq_canonical (r : I) (K : V.{u, v}) :
    NativeSymmetricFreeSource.freeModule.{u, v} r K =
      (letI : MonObj A.{u, v}.X := A.{u, v}.mon;
        (Mod.free A.{u, v}.X).obj
          (.mk ((evaluationLeftAdjoint V.{u, v} r).obj K))) :=
  eq_of_heq (actual_free_module_heq_canonical r K)

end NativeOmegaRecovery.NativeSymmetricSourceGEN.FreeSourceObjects

universe uI vI uV vV

namespace NativeOmegaRecovery.NativeSymmetricSourceGEN.OriginalDayGenerator

variable {I : Type uI} [Category.{vI} I] [MonoidalCategory I]
  {V : Type uV} [Category.{vV} V] [MonoidalCategory V]

theorem day_equivalence_adjunct (F : I ⥤ V) (G : DayFunctor I V)
    (t : (DayFunctor.equiv I V).symm.functor.obj F ⟶ G) :
    ((DayFunctor.equiv I V).symm.toAdjunction.homEquiv F G) t = t.natTrans := by
  have hu := Adjunction.homEquiv_unit (DayFunctor.equiv I V).symm.toAdjunction F G t
  have hv : (DayFunctor.equiv I V).symm.toAdjunction.unit.app F ≫
      (DayFunctor.equiv I V).symm.inverse.map t = t.natTrans :=
    Category.id_comp t.natTrans
  exact hu.trans hv

variable [∀ a b : I, HasCoproductsOfShape (a ⟶ b) V]

omit [MonoidalCategory I] [MonoidalCategory V] in
theorem evaluation_adjunct (i : I) (K : V) (F : I ⥤ V)
    (t : (evaluationLeftAdjoint V i).obj K ⟶ F) :
    ((evaluationAdjunctionRight V i).homEquiv K F) t =
      Sigma.ι (fun _ : i ⟶ i => K) (𝟙 i) ≫ t.app i := by
  simp only [evaluationAdjunctionRight, Adjunction.mkOfHomEquiv_homEquiv]
  rfl

variable [MonoidalCategory (DayFunctor I V)]

theorem original_day_adjunct (A : DayFunctor I V) [MonObj A]
    (i : I) (K : V) (N : Mod (DayFunctor I V) A)
    (f : (Mod.dayFreeAt A i).obj K ⟶ N) :
    ((Mod.dayFreeAtEvaluationAdjunction A i).homEquiv K N) f =
      Sigma.ι (fun _ : i ⟶ i => K) (𝟙 i) ≫
        (((Mod.freeForgetAdjunction A).homEquiv
          (DayFunctor.mk ((evaluationLeftAdjoint V i).obj K)) N f).natTrans.app i) := by
  let F := (evaluationLeftAdjoint V i).obj K
  let P : DayFunctor I V := .mk F
  let t : (DayFunctor.equiv I V).symm.functor.obj F ⟶ N.X :=
    (Mod.freeForgetAdjunction A).homEquiv P N f
  have hComparison := Mod.dayFreeAtEvaluationAdjunction_homEquiv A i K N
  have hApply := congrArg (fun e => e f) hComparison
  have hDay := day_equivalence_adjunct F N.X t
  have hOrdinary := congrArg ((evaluationAdjunctionRight V i).homEquiv K N.X.functor) hDay
  have hEvaluation := evaluation_adjunct i K N.X.functor t.natTrans
  exact hApply.trans (hOrdinary.trans hEvaluation)

theorem original_day_generator (A : DayFunctor I V) [MonObj A]
    (i : I) (K : V) (N : Mod (DayFunctor I V) A)
    (f : (Mod.dayFreeAt A i).obj K ⟶ N) :
    ((Mod.dayFreeAtEvaluationAdjunction A i).homEquiv K N) f =
      Sigma.ι (fun _ : i ⟶ i => K) (𝟙 i) ≫
        ((Mod.freeForgetAdjunction A).unit.app
          (DayFunctor.mk ((evaluationLeftAdjoint V i).obj K))).natTrans.app i ≫
        f.hom.natTrans.app i := by
  let P : DayFunctor I V := .mk ((evaluationLeftAdjoint V i).obj K)
  have h := original_day_adjunct A i K N f
  have hu := Adjunction.homEquiv_unit (Mod.freeForgetAdjunction A) P N f
  have hLift := congrArg
    (fun t : P ⟶ N.X => Sigma.ι (fun _ : i ⟶ i => K) (𝟙 i) ≫ t.natTrans.app i) hu
  have hComposition := DayFunctor.comp_natTrans
    ((Mod.freeForgetAdjunction A).unit.app P) f.hom
  have hComponent := congrArg (fun t => t.app i) hComposition
  exact h.trans (hLift.trans (congrArg
    (fun t => Sigma.ι (fun _ : i ⟶ i => K) (𝟙 i) ≫ t) hComponent))

theorem original_day_generator_two_maps (A : DayFunctor I V) [MonObj A]
    (i : I) (K : V) (M N : Mod (DayFunctor I V) A)
    (f : (Mod.dayFreeAt A i).obj K ⟶ M) (q : M ⟶ N) :
    ((Mod.dayFreeAtEvaluationAdjunction A i).homEquiv K N) (f ≫ q) =
      Sigma.ι (fun _ : i ⟶ i => K) (𝟙 i) ≫
        ((Mod.freeForgetAdjunction A).unit.app
          (DayFunctor.mk ((evaluationLeftAdjoint V i).obj K))).natTrans.app i ≫
        f.hom.natTrans.app i ≫ q.hom.natTrans.app i := by
  have h := original_day_generator A i K N (f ≫ q)
  have hComposition := DayFunctor.comp_natTrans f.hom q.hom
  have hComponent := congrArg (fun t => t.app i) hComposition
  exact h.trans (congrArg
    (fun t => Sigma.ι (fun _ : i ⟶ i => K) (𝟙 i) ≫
      ((Mod.freeForgetAdjunction A).unit.app
        (DayFunctor.mk ((evaluationLeftAdjoint V i).obj K))).natTrans.app i ≫ t) hComponent)


end NativeOmegaRecovery.NativeSymmetricSourceGEN.OriginalDayGenerator

private theorem original_source_arrow_transport_heq
    {W : Type uW} [Category.{vW} W] {M M' N : W} (h : M = M') (q : M ⟶ N) :
    HEq ((eqToIso h).inv ≫ q) q := by
  cases h
  exact heq_of_eq (Category.id_comp q)

private theorem generator_heq_of_original_data
    {I : Type uI} [Category.{vI} I] [MonoidalCategory I]
    {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
    [MonoidalCategory (DayFunctor I V)]
    [∀ a b : I, HasCoproductsOfShape (a ⟶ b) V]
    (R R' : DayFunctor I V) (m : MonObj R) (m' : MonObj R')
    (hR : R = R') (hm : HEq m m') (r : I) (K : V)
    (q : letI : MonObj R := m;
      (Mod.free R).obj (.mk ((evaluationLeftAdjoint V r).obj K)) ⟶ Mod.regular R)
    (q' : letI : MonObj R' := m';
      (Mod.free R').obj (.mk ((evaluationLeftAdjoint V r).obj K)) ⟶ Mod.regular R')
    (hq : HEq q q') :
    HEq (letI : MonObj R := m;
      Sigma.ι (fun _ : r ⟶ r => K) (𝟙 r) ≫
        ((Mod.freeForgetAdjunction R).unit.app
          (.mk ((evaluationLeftAdjoint V r).obj K))).natTrans.app r ≫
        q.hom.natTrans.app r)
      (letI : MonObj R' := m';
        Sigma.ι (fun _ : r ⟶ r => K) (𝟙 r) ≫
          ((Mod.freeForgetAdjunction R').unit.app
            (.mk ((evaluationLeftAdjoint V r).obj K))).natTrans.app r ≫
          q'.hom.natTrans.app r) := by
  cases hR
  cases hm
  cases hq
  rfl

namespace NativeOmegaRecovery.NativeSymmetricSourceGEN.NativeAdjointData

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

/-- The same actual original module arrow is carried only through its
proved whole free-source object equality. -/
def canonicalMap (r : Operad.SmallFinBijGroupoid) (K : PointedCGWH.{u, v})
    (q : NativeSymmetricFreeSource.freeModule.{u, v} r K ⟶
      Mod.regular PointedCGWH.sphereSequence.{u, v}) :
    (letI : MonObj PointedCGWH.sphereSequenceCommMon.{u, v}.X :=
      PointedCGWH.sphereSequenceCommMon.{u, v}.mon;
      (Mod.free PointedCGWH.sphereSequenceCommMon.{u, v}.X).obj
        (.mk ((evaluationLeftAdjoint PointedCGWH.{u, v} r).obj K)) ⟶
          Mod.regular PointedCGWH.sphereSequenceCommMon.{u, v}.X) :=
  (eqToIso (FreeSourceObjects.actual_free_module_eq_canonical.{u, v} r K)).inv ≫ q

/-- The entire original source map is preserved before any adjunct,
free-unit component or scalar generator is projected. -/
theorem canonicalMap_heq_original (r : Operad.SmallFinBijGroupoid) (K : PointedCGWH.{u, v})
    (q : NativeSymmetricFreeSource.freeModule.{u, v} r K ⟶
      Mod.regular PointedCGWH.sphereSequence.{u, v}) :
    HEq (canonicalMap.{u, v} r K q) q :=
  original_source_arrow_transport_heq
    (FreeSourceObjects.actual_free_module_eq_canonical.{u, v} r K) q

/-- Every actual scalar generator retains the original Day free adjunct
under the full original coefficient object, monoid and source-map data. -/
theorem canonical_generator_eq_original_day_adjunct
    (r : Operad.SmallFinBijGroupoid) (K : PointedCGWH.{u, v})
    (q : NativeSymmetricFreeSource.freeModule.{u, v} r K ⟶
      Mod.regular PointedCGWH.sphereSequence.{u, v}) :
    @Eq (K ⟶ PointedCGWH.sphereSequence.{u, v}.functor.obj r)
      (letI : MonObj PointedCGWH.sphereSequenceCommMon.{u, v}.X :=
        PointedCGWH.sphereSequenceCommMon.{u, v}.mon;
        Sigma.ι (fun _ : r ⟶ r => K) (𝟙 r) ≫
          ((Mod.freeForgetAdjunction PointedCGWH.sphereSequenceCommMon.{u, v}.X).unit.app
            (.mk ((evaluationLeftAdjoint PointedCGWH.{u, v} r).obj K))).natTrans.app r ≫
          (canonicalMap.{u, v} r K q).hom.natTrans.app r)
      ((Mod.dayFreeAtEvaluationAdjunction PointedCGWH.sphereSequence.{u, v} r).homEquiv
        K (Mod.regular PointedCGWH.sphereSequence.{u, v}) q) := by
  have hOriginal := OriginalDayGenerator.original_day_generator
    PointedCGWH.sphereSequence.{u, v} r K (Mod.regular PointedCGWH.sphereSequence.{u, v}) q
  have hData := generator_heq_of_original_data
    PointedCGWH.sphereSequenceCommMon.{u, v}.X PointedCGWH.sphereSequence.{u, v}
    PointedCGWH.sphereSequenceCommMon.{u, v}.mon PointedCGWH.sphereSequenceMonObj.{u, v}
    NativeScalarCoefficient.sphereCoefficient_obj_eq.{u, v}
    (heq_of_eq NativeScalarCoefficient.sphereCoefficient_mon_eq.{u, v}) r K
    (canonicalMap.{u, v} r K q) q (canonicalMap_heq_original.{u, v} r K q)
  exact (eq_of_heq hData).trans hOriginal.symm

end NativeOmegaRecovery.NativeSymmetricSourceGEN.NativeAdjointData

namespace NativeOmegaRecovery.NativeSymmetricSourceGEN.ActualSourceFunctor
private abbrev I := Operad.SmallFinBijGroupoid
private abbrev V := PointedCGWH.{u, v}
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

private abbrev A := PointedCGWH.sphereSequenceCommMon.{u, v}
private abbrev E := PointedCGWH.SymmetricModulePresentation.moduleOperatorEquivalence.{u, v}

/-- The whole original source functor is the original module transport with
the SAME coefficient, equivalence, source and target choices. -/
theorem sourceFunctor_original :
    NativeOmegaPreparation.SymmetricFunction.sourceFunctor.{u, v} =
      NativeOmegaPreparation.ModuleFunctionTransport.sourceFunctor A.{u, v} E.{u, v} := rfl

/-- Every entire original native free-function source is the actual original
source-functor value before any input or coordinate is selected. -/
theorem free_sourceFunctor_obj_original (r : I) (M : V.{u, v}) :
    NativeOmegaPreparation.SymmetricFunction.functor.{u, v} r M =
      (NativeOmegaPreparation.ModuleFunctionTransport.sourceFunctor A.{u, v} E.{u, v}).obj
        (.op (NativeSymmetricFreeSource.freeModule.{u, v} r M)) := rfl

/-- Source variance is the SAME original whole functor map on the SAME module
arrow before any input or coordinate is selected. -/
theorem free_sourceFunctor_map_original {r s : I} {M M' : V.{u, v}}
    (f : NativeSymmetricFreeSource.freeModule.{u, v} s M' ⟶
      NativeSymmetricFreeSource.freeModule.{u, v} r M) :
    NativeOmegaPreparation.SymmetricFunction.precompose.{u, v}
        (n := r) (k := s) (M := M) (N := M') f =
      (NativeOmegaPreparation.ModuleFunctionTransport.sourceFunctor A.{u, v} E.{u, v}).map
        f.op := rfl

end NativeOmegaRecovery.NativeSymmetricSourceGEN.ActualSourceFunctor
