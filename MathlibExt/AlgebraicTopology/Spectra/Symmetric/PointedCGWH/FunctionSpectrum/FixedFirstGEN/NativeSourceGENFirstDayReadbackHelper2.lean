/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.Spectra.Symmetric.PointedCGWH.FunctionSpectrum.SourceCoefficientSourceData
import MathlibExt.AlgebraicTopology.Spectra.Symmetric.PointedCGWH.StabilizationTarget

/-!
# Evaluation of the first symmetric stabilization generator

The first symmetric stabilization arrow is compared in the Day-module and operator
presentations through their free-evaluation adjunctions. The formulas retain the coproduct
insertion, free-module unit and both component maps of a composite. Evaluation after the
zero-degree free contraction into the regular module identifies the coefficient map with the
inverse of the first-coefficient isomorphism.
-/

set_option autoImplicit false
noncomputable section
universe u v uW vW uJ
open CategoryTheory MonoidalCategory Limits
open CategoryTheory.EnrichedFunctorCat
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK
open scoped MonoidalClosed CategoryTheory.MonObj

private theorem transportValue {A B : Sort _} (f : A → B)
    {x y : A} {z : B} (hxy : x = y) (hx : f x = z) : f y = z :=
  (congrArg f hxy).symm.trans hx

private theorem evaluate_stabilization
    {W : Type uW} [Category.{vW} W] [MonoidalCategory W] [BraidedCategory W]
    [MonoidalClosed W] {J : Type uJ} [EnrichedCategory W J]
    (a b : J) (K : W) (D : K ⟶ (a ⟶[W] b)) :
    Free.evaluate b K (Free.object a (𝟙_ W)) (CurrentFree.stabilization a b K D) =
      D ≫ (λ_ (a ⟶[W] b)).inv := by
  have h := CurrentFree.stabilization_adjunct a b K D
  have he := congrArg
    (fun e => e K (Free.object a (𝟙_ W)) (CurrentFree.stabilization a b K D))
    (Free.adjunction_homEquiv b)
  exact he.symm.trans h

namespace NativeOmegaRecovery.NativeSymmetricSourceGEN.FirstCoefficient.DayReadback

private abbrev I := Operad.SmallFinBijGroupoid
private abbrev V := PointedCGWH.{u, v}
private abbrev S := PointedCGWH.sphereSequence.{u, v}
private abbrev first := NativeSymmetricDelooping.firstIndex
private abbrev P₁ : DayFunctor I V.{u, v} :=
  .mk ((evaluationLeftAdjoint V.{u, v} first).obj PointedCGWH.sphereOne.{u, v})

attribute [local instance] Operad.SmallFinBijGroupoid.instMonoidalCategory
  Operad.SmallFinBijGroupoid.instSymmetricCategory
  PointedCGWH.copowerUnderlyingEnrichedOrdinary PointedCGWH.copowerUnderlyingMonoidal
  PointedCGWH.sphereSequenceMonObj PointedCGWH.sphereSequenceIsCommMonObj
  MonoidalClosed.enrichedCategorySelf MonoidalClosed.enrichedOrdinaryCategorySelf
  PointedCGWH.EnrichedMapping.hasSmallLimits
  NativeOmegaPreparation.SymmetricFunction.sequenceCoequalizers
  NativeOmegaPreparation.SymmetricFunction.sequenceEqualizers
  NativeOmegaPreparation.SymmetricFunction.sequenceClosed
  PointedCGWH.originalSymmetricSequenceMonoidal
  PointedCGWH.originalSymmetricSequenceBraided PointedCGWH.originalSymmetricSequenceSymmetric

open PointedCGWH.SymmetricModulePresentation
open NativeSymmetricFreeSource

private def regularOperator :
    EnrichedFunctorCat V.{u, v} PointedCGWH.SymmetricOperatorIndex.{u, v} :=
  toOperatorFunctor (Mod.regular S.{u, v})

private def regularUnitExtension :
    nativeFree.{u, v} (𝟙_ I) (𝟙_ V.{u, v}) ⟶ regularOperator.{u, v} :=
  Free.extend (V := V.{u, v}) (A := PointedCGWH.SymmetricOperatorIndex.{u, v})
    (PointedCGWH.symmetricOperatorObj.{u, v} (𝟙_ I)) (𝟙_ V.{u, v})
    regularOperator.{u, v} PointedCGWH.sphereCopowerLaxData.{u, v}.epsilon


set_option backward.isDefEq.respectTransparency false in
/-- The same complete zero native source contracts to the chosen regular sphere extension. -/
private theorem regular_unit_extension_eq_zero_native_source :
    (NativeOmegaPreparation.SymmetricNativeFree.operatorComparison.{u, v} (𝟙_ I)).inv.app
        (𝟙_ V.{u, v}) ≫ moduleToOperator.{u, v}.map actualZeroFreeContraction.{u, v} =
      regularUnitExtension.{u, v} := by
  simpa only [regularUnitExtension, regularOperator] using
    actualZeroFreeContraction_native_extend.{u, v}

/-- The complete original first free-module source arrow before taking its Day adjunct. -/
def originalFirstModuleArrow : freeModule.{u, v} first PointedCGWH.sphereOne.{u, v} ⟶
    freeModule.{u, v} (𝟙_ I) (𝟙_ V.{u, v}) :=
  sourceArrow.{u, v} (r := (𝟙_ I)) (s := first)
    (M := (𝟙_ V.{u, v})) (M' := PointedCGWH.sphereOne.{u, v})
    NativeSymmetricLambda.firstSource.{u, v}

theorem originalFirstModuleArrow_original : originalFirstModuleArrow.{u, v} =
    sourceArrow.{u, v} (r := (𝟙_ I)) (s := first)
      (M := (𝟙_ V.{u, v})) (M' := PointedCGWH.sphereOne.{u, v})
      NativeSymmetricLambda.firstSource.{u, v} := rfl

theorem original_first_day_generator_two_maps
    (f : freeModule.{u, v} first PointedCGWH.sphereOne.{u, v} ⟶
      freeModule.{u, v} (𝟙_ I) (𝟙_ V.{u, v}))
    (q : freeModule.{u, v} (𝟙_ I) (𝟙_ V.{u, v}) ⟶ Mod.regular S.{u, v}) :
    ((Mod.dayFreeAtEvaluationAdjunction S.{u, v} first).homEquiv
      PointedCGWH.sphereOne.{u, v} (Mod.regular S.{u, v})) (f ≫ q) =
    Sigma.ι (fun _ : first ⟶ first => PointedCGWH.sphereOne.{u, v}) (𝟙 first) ≫
      ((Mod.freeForgetAdjunction S.{u, v}).unit.app P₁.{u, v}).natTrans.app first ≫
      f.hom.natTrans.app first ≫ q.hom.natTrans.app first := by
  exact OriginalDayGenerator.original_day_generator_two_maps
    (I := I) (V := V.{u, v}) S.{u, v} first PointedCGWH.sphereOne.{u, v}
    (freeModule.{u, v} (𝟙_ I) (𝟙_ V.{u, v})) (Mod.regular S.{u, v}) f q


/-- The original free-source isomorphisms commute with every whole native source arrow. -/
theorem original_operator_source_square {r s : I} {K K' : V.{u, v}}
    (f : nativeFree.{u, v} s K' ⟶ nativeFree.{u, v} r K) :
    (NativeOmegaPreparation.SymmetricNativeFree.operatorComparison.{u, v} s).inv.app K' ≫
        moduleToOperator.{u, v}.map (sourceArrow.{u, v} f) =
      f ≫ (NativeOmegaPreparation.SymmetricNativeFree.operatorComparison.{u, v} r).inv.app K := by
  have h := ModuleFreeSourceTransport.operatorComparison_inv_source
    PointedCGWH.sphereSequenceCommMon.{u, v} moduleOperatorEquivalence.{u, v}
    (freeIso.{u, v} r K) (freeIso.{u, v} s K') f
  have hr := ModuleFreeAdjunctTransport.operatorComparison_eq
    PointedCGWH.sphereSequenceCommMon.{u, v} moduleOperatorEquivalence.{u, v}
    (PointedCGWH.symmetricOperatorObj.{u, v} r)
    (Mod.dayFreeAt S.{u, v} r) (Mod.dayEvaluation S.{u, v} r)
    (Mod.dayFreeAtEvaluationAdjunction S.{u, v} r)
    (NativeOmegaPreparation.SymmetricNativeFree.evaluationIso.{u, v} r) K
  have hs := ModuleFreeAdjunctTransport.operatorComparison_eq
    PointedCGWH.sphereSequenceCommMon.{u, v} moduleOperatorEquivalence.{u, v}
    (PointedCGWH.symmetricOperatorObj.{u, v} s)
    (Mod.dayFreeAt S.{u, v} s) (Mod.dayEvaluation S.{u, v} s)
    (Mod.dayFreeAtEvaluationAdjunction S.{u, v} s)
    (NativeOmegaPreparation.SymmetricNativeFree.evaluationIso.{u, v} s) K'
  have hr' : ModuleFreeSourceTransport.operatorComparison
      PointedCGWH.sphereSequenceCommMon.{u, v} moduleOperatorEquivalence.{u, v}
      (freeIso.{u, v} r K) =
        (NativeOmegaPreparation.SymmetricNativeFree.operatorComparison.{u, v} r).app K := hr
  have hs' : ModuleFreeSourceTransport.operatorComparison
      PointedCGWH.sphereSequenceCommMon.{u, v} moduleOperatorEquivalence.{u, v}
      (freeIso.{u, v} s K') =
        (NativeOmegaPreparation.SymmetricNativeFree.operatorComparison.{u, v} s).app K' := hs
  exact (congrArg (fun q => q ≫ moduleToOperator.{u, v}.map (sourceArrow.{u, v} f))
      (congrArg Iso.inv hs')).symm.trans
    (h.trans (congrArg (fun q => f ≫ q) (congrArg Iso.inv hr')))

namespace OriginalDayPoint

private abbrev I := Operad.SmallFinBijGroupoid
private abbrev V := PointedCGWH.{u, v}
private abbrev J := PointedCGWH.SymmetricOperatorIndex.{u, v}
private abbrev S := PointedCGWH.sphereSequence.{u, v}
private abbrev first := NativeSymmetricDelooping.firstIndex
private abbrev Module := NativeSymmetricFreeFunction.OriginalModule.{u, v}

attribute [local instance] Operad.SmallFinBijGroupoid.instMonoidalCategory
  Operad.SmallFinBijGroupoid.instSymmetricCategory
  PointedCGWH.copowerUnderlyingEnrichedOrdinary PointedCGWH.copowerUnderlyingMonoidal
  PointedCGWH.sphereSequenceMonObj PointedCGWH.sphereSequenceIsCommMonObj
  MonoidalClosed.enrichedCategorySelf MonoidalClosed.enrichedOrdinaryCategorySelf
  PointedCGWH.EnrichedMapping.hasSmallLimits
  NativeOmegaPreparation.SymmetricFunction.sequenceCoequalizers
  NativeOmegaPreparation.SymmetricFunction.sequenceEqualizers
  NativeOmegaPreparation.SymmetricFunction.sequenceClosed
  PointedCGWH.originalSymmetricSequenceMonoidal
  PointedCGWH.originalSymmetricSequenceBraided PointedCGWH.originalSymmetricSequenceSymmetric

open PointedCGWH.SymmetricModulePresentation
open NativeSymmetricFreeSource

private abbrev X := PointedCGWH.sphereOne.{u, v}
private abbrev M : Module.{u, v} := Mod.regular S.{u, v}
private abbrev a := PointedCGWH.symmetricOperatorObj.{u, v} first
private abbrev L := Mod.dayFreeAt S.{u, v} first
private abbrev R := Mod.dayEvaluation S.{u, v} first
private abbrev A := Mod.dayFreeAtEvaluationAdjunction S.{u, v} first
private abbrev E := moduleOperatorEquivalence.{u, v}
private abbrev U := NativeOmegaPreparation.SymmetricNativeFree.evaluationIso.{u, v} first
private abbrev P := NativeOmegaPreparation.SymmetricNativeFree.operatorComparison.{u, v} first

/-- The native Day adjunct is the same complete original operator-evaluation word. -/
private theorem regularDayPoint (g : freeModule.{u, v} first X.{u, v} ⟶ M.{u, v}) :
    A.{u, v}.homEquiv X.{u, v} M.{u, v} g =
    Free.evaluate (V := V.{u, v}) (A := J.{u, v}) a X.{u, v} (E.functor.obj M.{u, v})
      (P.inv.app X.{u, v} ≫ E.functor.map g) := by
  let lhs : X.{u, v} ⟶ S.{u, v}.functor.obj first := A.homEquiv X M g
  have hPoint := FreeAdjunctionSource.point
    (V := V.{u, v}) (J := J.{u, v}) (C := Module.{u, v})
    (X := X.{u, v}) (M := M.{u, v}) E a L R A U g
  have hUnit : U.inv.app M.{u, v} = 𝟙 (S.{u, v}.functor.obj first) := rfl
  have hRemove : lhs ≫ U.inv.app M.{u, v} = lhs :=
    (congrArg (fun t : S.{u, v}.functor.obj first ⟶ S.{u, v}.functor.obj first => lhs ≫ t)
      hUnit).trans (Category.comp_id lhs)
  have hInitializer : P.{u, v} = FreeAdjunctionSource.operatorIso E a L R A U :=
    NativeSymmetricSourceComposite.operatorComparison_eq_initializer.{u, v} first
  have hProjection := congrArg
    (fun e : L ⋙ E.functor ≅ Free.functor (V := V.{u, v}) a =>
      Free.evaluate (V := V.{u, v}) (A := J.{u, v}) a X.{u, v} (E.functor.obj M.{u, v})
        (e.inv.app X.{u, v} ≫ E.functor.map g)) hInitializer
  exact hRemove.symm.trans (hPoint.trans hProjection.symm)


end OriginalDayPoint

private theorem original_regular_day_point_normalized
    (g : freeModule.{u, v} first PointedCGWH.sphereOne.{u, v} ⟶ Mod.regular S.{u, v}) :
    (Mod.dayFreeAtEvaluationAdjunction S.{u, v} first).homEquiv
        PointedCGWH.sphereOne.{u, v} (Mod.regular S.{u, v}) g =
      Free.evaluate (V := V.{u, v}) (A := PointedCGWH.SymmetricOperatorIndex.{u, v})
        (PointedCGWH.symmetricOperatorObj.{u, v} first) PointedCGWH.sphereOne.{u, v} regularOperator.{u, v}
        ((NativeOmegaPreparation.SymmetricNativeFree.operatorComparison.{u, v} first).inv.app
          PointedCGWH.sphereOne.{u, v} ≫ moduleToOperator.{u, v}.map g) := by
  have h := OriginalDayPoint.regularDayPoint.{u, v} g
  dsimp only [OriginalDayPoint.I, OriginalDayPoint.V, OriginalDayPoint.J, OriginalDayPoint.S,
    OriginalDayPoint.first, OriginalDayPoint.Module, OriginalDayPoint.X, OriginalDayPoint.M,
    OriginalDayPoint.a, OriginalDayPoint.L, OriginalDayPoint.R, OriginalDayPoint.A, OriginalDayPoint.E,
    OriginalDayPoint.U, OriginalDayPoint.P] at h
  dsimp only [moduleOperatorEquivalence] at h
  dsimp only [regularOperator, I, V, S, first]
  exact h

/-- The sphere tensor-power functor respects the braiding of finite bijections. -/
local instance sphereFunctorBraided : S.{u, v}.functor.Braided :=
  Operad.SmallFinBijGroupoid.tensorPowerFunctorBraided PointedCGWH.sphereOne.{u, v}

/-- The full sphere-unit extension evaluates the actual coend generator using the
regular module action, the original right unit law, and the final index braid. -/
theorem regular_unit_extension_generator (r : I) :
    Actual.symmetricNu.{u, v} (𝟙_ I) r ≫
        (λ_ (PointedCGWH.symmetricOperatorObj.{u, v} (𝟙_ I) ⟶[V.{u, v}]
          PointedCGWH.symmetricOperatorObj.{u, v} ((𝟙_ I) ⊗ r))).inv ≫
        component (Free.extend (PointedCGWH.symmetricOperatorObj.{u, v} (𝟙_ I))
          (𝟙_ V.{u, v}) (toOperatorFunctor (Mod.regular S.{u, v}))
          PointedCGWH.sphereCopowerLaxData.{u, v}.epsilon)
          (PointedCGWH.symmetricOperatorObj.{u, v} ((𝟙_ I) ⊗ r)) =
      S.{u, v}.functor.map (λ_ r).inv := by
  let N := Mod.regular S.{u, v}
  let p := (ρ_ (S.{u, v}.functor.obj r)).inv ≫
    (S.{u, v}.functor.obj r ◁ PointedCGWH.sphereCopowerLaxData.{u, v}.epsilon)
  have hRaw := raw_unit_extension_generator
    (PointedCGWH.symmetricOperatorObj.{u, v} (𝟙_ I))
    (PointedCGWH.symmetricOperatorObj.{u, v} ((𝟙_ I) ⊗ r))
    (S.{u, v}.functor.obj r) (Actual.symmetricNu.{u, v} (𝟙_ I) r)
    (toOperatorFunctor N) PointedCGWH.sphereCopowerLaxData.{u, v}.epsilon
  have hAction :
      CurrentFree.action (PointedCGWH.symmetricOperatorObj.{u, v} (𝟙_ I))
          (PointedCGWH.symmetricOperatorObj.{u, v} ((𝟙_ I) ⊗ r))
          (S.{u, v}.functor.obj r) (Actual.symmetricNu.{u, v} (𝟙_ I) r)
          (toOperatorFunctor N) =
        pairAction N r (𝟙_ I) ≫ S.{u, v}.functor.map (β_ r (𝟙_ I)).hom :=
    (CurrentFree.action_operatorGenerator_eq_reconstructed (toOperatorFunctor N)
      r (𝟙_ I) ((𝟙_ I) ⊗ r) (β_ r (𝟙_ I)).hom).trans
      (reconstructedArrowAction_forward N r (𝟙_ I) ((𝟙_ I) ⊗ r) (β_ r (𝟙_ I)).hom)
  have hPair : pairAction N r (𝟙_ I) =
      Functor.LaxMonoidal.μ S.{u, v}.functor r (𝟙_ I) :=
    PointedCGWH.sphereCopowerLaxData_mul.{u, v} r (𝟙_ I)
  have hUnit := Functor.LaxMonoidal.right_unitality_inv S.{u, v}.functor r
  have hIndex : (ρ_ r).inv ≫ (β_ r (𝟙_ I)).hom = (λ_ r).inv :=
    rightUnitor_inv_braiding r
  have hPrefix : p ≫ pairAction N r (𝟙_ I) = S.{u, v}.functor.map (ρ_ r).inv :=
    (congrArg (fun q => p ≫ q) hPair).trans hUnit
  have hActionPrefix : p ≫ CurrentFree.action
      (PointedCGWH.symmetricOperatorObj.{u, v} (𝟙_ I))
      (PointedCGWH.symmetricOperatorObj.{u, v} ((𝟙_ I) ⊗ r))
      (S.{u, v}.functor.obj r) (Actual.symmetricNu.{u, v} (𝟙_ I) r)
      (toOperatorFunctor N) =
        S.{u, v}.functor.map (ρ_ r).inv ≫ S.{u, v}.functor.map (β_ r (𝟙_ I)).hom :=
    (congrArg (fun q => p ≫ q) hAction).trans
      ((Category.assoc _ _ _).symm.trans
        (congrArg (fun q => q ≫ S.{u, v}.functor.map (β_ r (𝟙_ I)).hom) hPrefix))
  exact hRaw.trans (hActionPrefix.trans
    ((S.{u, v}.functor.map_comp (ρ_ r).inv (β_ r (𝟙_ I)).hom).symm.trans
      (congrArg S.{u, v}.functor.map hIndex)))

theorem unitStabilization_regular_evaluate (r : I) :
    Free.evaluate (PointedCGWH.symmetricOperatorObj.{u, v} ((𝟙_ I) ⊗ r))
      (S.{u, v}.functor.obj r) regularOperator.{u, v}
      (NativeSymmetricLambda.unitStabilization.{u, v} r ≫ regularUnitExtension.{u, v}) =
      S.{u, v}.functor.map (λ_ r).inv := by
  let b := PointedCGWH.symmetricOperatorObj.{u, v} ((𝟙_ I) ⊗ r)
  have hStab : Free.evaluate b (S.{u, v}.functor.obj r)
      (nativeFree.{u, v} (𝟙_ I) (𝟙_ V.{u, v}))
      (NativeSymmetricLambda.unitStabilization.{u, v} r) =
    Actual.symmetricNu.{u, v} (𝟙_ I) r ≫
      (λ_ (PointedCGWH.symmetricOperatorObj.{u, v} (𝟙_ I) ⟶[V.{u, v}] b)).inv :=
    evaluate_stabilization (PointedCGWH.symmetricOperatorObj.{u, v} (𝟙_ I)) b
      (S.{u, v}.functor.obj r) (Actual.symmetricNu.{u, v} (𝟙_ I) r)
  have hPost := Free.evaluate_postcomp b (S.{u, v}.functor.obj r)
    (NativeSymmetricLambda.unitStabilization.{u, v} r) regularUnitExtension.{u, v}
  exact hPost.trans ((congrArg (fun f => f ≫ component regularUnitExtension.{u, v} b)
    hStab).trans (regular_unit_extension_generator r))

/-- The actual first native source followed by that same original sphere-unit
extension evaluates to the original one-sphere coefficient inverse. -/
theorem original_first_source_extension_evaluate :
    Free.evaluate (V := V.{u, v}) (A := PointedCGWH.SymmetricOperatorIndex.{u, v})
      (PointedCGWH.symmetricOperatorObj.{u, v} first)
      PointedCGWH.sphereOne.{u, v} regularOperator.{u, v}
      (NativeSymmetricLambda.firstSource.{u, v} ≫ regularUnitExtension.{u, v}) =
      NativeSymmetricDelooping.firstCoefficientIso.{u, v}.inv := by
  let e := regularUnitExtension.{u, v}
  have hUnit : Free.evaluate (PointedCGWH.symmetricOperatorObj.{u, v} first)
      (S.{u, v}.functor.obj first) (toOperatorFunctor (Mod.regular S.{u, v}))
      (NativeSymmetricLambda.unitStabilization.{u, v} first ≫ e) =
    S.{u, v}.functor.map (λ_ first).inv := unitStabilization_regular_evaluate first
  have hArrow : NativeSymmetricLambda.firstSource.{u, v} ≫ e =
      Free.coefficientMap (PointedCGWH.symmetricOperatorObj.{u, v} first)
        NativeSymmetricDelooping.firstCoefficientIso.{u, v}.inv ≫
          (NativeSymmetricLambda.unitStabilization.{u, v} first ≫ e) :=
    (congrArg (fun f => f ≫ e) NativeSymmetricLambda.firstSource_original.{u, v}).trans
      (Category.assoc _ _ _)
  have hPre := Free.evaluate_precomp (PointedCGWH.symmetricOperatorObj.{u, v} first)
    (toOperatorFunctor (Mod.regular S.{u, v}))
    NativeSymmetricDelooping.firstCoefficientIso.{u, v}.inv
    (NativeSymmetricLambda.unitStabilization.{u, v} first ≫ e)
  have hIndex : (λ_ first).inv = 𝟙 first := by
    apply Core.hom_ext
    funext x
    have hs : Subsingleton (ULift.{0, 0} (Fin first.of.len)) := by
      change Subsingleton (ULift.{0, 0} (Fin 1))
      infer_instance
    exact @Subsingleton.elim _ hs _ _
  have hMap : S.{u, v}.functor.map (λ_ first).inv = 𝟙 (S.{u, v}.functor.obj first) :=
    (congrArg S.{u, v}.functor.map hIndex).trans (S.{u, v}.functor.map_id first)
  exact (congrArg (Free.evaluate (PointedCGWH.symmetricOperatorObj.{u, v} first)
      PointedCGWH.sphereOne.{u, v} (toOperatorFunctor (Mod.regular S.{u, v}))) hArrow).trans
    (hPre.trans ((congrArg (fun f => NativeSymmetricDelooping.firstCoefficientIso.{u, v}.inv ≫ f)
      hUnit).trans ((congrArg (fun f => NativeSymmetricDelooping.firstCoefficientIso.{u, v}.inv ≫ f)
        hMap).trans (Category.comp_id _))))

set_option backward.isDefEq.respectTransparency false in
/-- The entire first source and same zero contraction commute with the actual operator comparison. -/
private theorem first_source_contraction_operator_square :
    (NativeOmegaPreparation.SymmetricNativeFree.operatorComparison.{u, v} first).inv.app
        PointedCGWH.sphereOne.{u, v} ≫ moduleToOperator.{u, v}.map
          (originalFirstModuleArrow.{u, v} ≫ actualZeroFreeContraction.{u, v}) =
      NativeSymmetricLambda.firstSource.{u, v} ≫ regularUnitExtension.{u, v} := by
  have hSquare := original_operator_source_square.{u, v}
    (r := (𝟙_ I)) (s := first) (K := (𝟙_ V.{u, v})) (K' := PointedCGWH.sphereOne.{u, v})
    NativeSymmetricLambda.firstSource.{u, v}
  have hUnit := regular_unit_extension_eq_zero_native_source.{u, v}
  let a := (NativeOmegaPreparation.SymmetricNativeFree.operatorComparison.{u, v} first).inv.app
    PointedCGWH.sphereOne.{u, v}
  let b := (NativeOmegaPreparation.SymmetricNativeFree.operatorComparison.{u, v} (𝟙_ I)).inv.app
    (𝟙_ V.{u, v})
  let t := moduleToOperator.{u, v}.map originalFirstModuleArrow.{u, v}
  let q := moduleToOperator.{u, v}.map actualZeroFreeContraction.{u, v}
  let f := NativeSymmetricLambda.firstSource.{u, v}
  let e := regularUnitExtension.{u, v}
  have hSquare' : a ≫ t = f ≫ b := by
    simpa only [a, t, f, b, originalFirstModuleArrow] using hSquare
  have hUnit' : b ≫ q = e := hUnit
  have hArrow :
      a ≫ moduleToOperator.{u, v}.map
          (originalFirstModuleArrow.{u, v} ≫ actualZeroFreeContraction.{u, v}) =
        f ≫ e := by
    rw [moduleToOperator.{u, v}.map_comp]
    change a ≫ (t ≫ q) = f ≫ e
    rw [← Category.assoc, hSquare', Category.assoc, hUnit']
  exact hArrow

/-- The actual contracted first source is retained as a complete module arrow. -/
private def actual_first_contraction :
    freeModule.{u, v} first PointedCGWH.sphereOne.{u, v} ⟶ Mod.regular S.{u, v} :=
  originalFirstModuleArrow.{u, v} ≫ actualZeroFreeContraction.{u, v}

private theorem actual_first_contraction_original :
    actual_first_contraction.{u, v} = originalFirstModuleArrow.{u, v} ≫
      actualZeroFreeContraction.{u, v} := rfl

private theorem actual_first_contraction_operator_square :
    (NativeOmegaPreparation.SymmetricNativeFree.operatorComparison.{u, v} first).inv.app
      PointedCGWH.sphereOne.{u, v} ≫ moduleToOperator.{u, v}.map actual_first_contraction.{u, v} =
      NativeSymmetricLambda.firstSource.{u, v} ≫ regularUnitExtension.{u, v} := by
  have h := congrArg
    (fun g : freeModule.{u, v} first PointedCGWH.sphereOne.{u, v} ⟶ Mod.regular S.{u, v} =>
      (NativeOmegaPreparation.SymmetricNativeFree.operatorComparison.{u, v} first).inv.app
        PointedCGWH.sphereOne.{u, v} ≫ moduleToOperator.{u, v}.map g)
    actual_first_contraction_original.{u, v}
  exact h.trans first_source_contraction_operator_square.{u, v}

private theorem actual_first_contraction_generator :
    (Mod.dayFreeAtEvaluationAdjunction S.{u, v} first).homEquiv
        PointedCGWH.sphereOne.{u, v} (Mod.regular S.{u, v}) actual_first_contraction.{u, v} =
      NativeSymmetricDelooping.firstCoefficientIso.{u, v}.inv := by
  have hPoint := original_regular_day_point_normalized.{u, v} actual_first_contraction.{u, v}
  have hEvaluate := congrArg
    (fun t : nativeFree.{u, v} first PointedCGWH.sphereOne.{u, v} ⟶ regularOperator.{u, v} =>
      Free.evaluate (PointedCGWH.symmetricOperatorObj.{u, v} first)
        PointedCGWH.sphereOne.{u, v} regularOperator.{u, v} t)
    actual_first_contraction_operator_square.{u, v}
  exact hPoint.trans (hEvaluate.trans original_first_source_extension_evaluate.{u, v})

set_option backward.isDefEq.respectTransparency false in
/-- The same entire original first module source and zero-free contraction
have that original coefficient inverse under the actual Day adjunction. -/
theorem original_first_source_contracted_generator :
    (Mod.dayFreeAtEvaluationAdjunction S.{u, v} first).homEquiv
        PointedCGWH.sphereOne.{u, v} (Mod.regular S.{u, v})
        (originalFirstModuleArrow.{u, v} ≫ actualZeroFreeContraction.{u, v}) =
      NativeSymmetricDelooping.firstCoefficientIso.{u, v}.inv := by
  exact transportValue
    ((Mod.dayFreeAtEvaluationAdjunction S.{u, v} first).homEquiv
      PointedCGWH.sphereOne.{u, v} (Mod.regular S.{u, v}))
    actual_first_contraction_original.{u, v} actual_first_contraction_generator.{u, v}




end NativeOmegaRecovery.NativeSymmetricSourceGEN.FirstCoefficient.DayReadback
