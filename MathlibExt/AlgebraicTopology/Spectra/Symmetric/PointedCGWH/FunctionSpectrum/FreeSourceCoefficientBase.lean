/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.SymmetricFreeSmashComparison
import MathlibExt.AlgebraicTopology.Spectra.Symmetric.PointedCGWH.FunctionSpectrum.FreeSource

/-!
# Original symmetric free-function coefficient and target source maps

The actual free-source isomorphisms retain every coefficient map through both
module and native source variance. The target scalar map is the original
cotensor pre-map, and the complete comparison retains the existing carrier
counits and every finite output index.
-/

set_option autoImplicit false
noncomputable section
universe u v
open CategoryTheory MonoidalCategory Limits
open CategoryTheory.EnrichedFunctorCat
open scoped MonoidalClosed CGWH.limits CategoryTheory.MonObj

namespace NativeOmegaRecovery.FreeAdjunctionCoefficientSource
universe uC vC uV vV uJ
variable {C : Type uC} [Category.{vC} C] [MonoidalCategory C] [BraidedCategory C]
  [MonoidalClosed C] [HasEqualizers C] [HasCoequalizers C]
  {V : Type uV} [Category.{vV} V] [MonoidalCategory V] [BraidedCategory V]
  [MonoidalClosed V] {J : Type uJ} [EnrichedCategory V J]
  (A : CommMon C) (E : Mod C A.X ≌ EnrichedFunctorCat V J)
  (a : J) (L : V ⥤ Mod C A.X) (e : L ≅ Free.functor a ⋙ E.inverse)

omit [MonoidalClosed C] [HasEqualizers C] [HasCoequalizers C] in
/-- The free-source transport of a coefficient arrow agrees with the given
coefficient functor's map. -/
theorem sourceArrow_coefficient {M' M : V} (f : M' ⟶ M) :
    NativeOmegaRecovery.ModuleFreeSourceTransport.sourceArrow A E
        (e.app M) (e.app M') (Free.coefficientMap a f) = L.map f := by
  unfold NativeOmegaRecovery.ModuleFreeSourceTransport.sourceArrow
  simp only [Iso.app_hom, Iso.app_inv]
  exact NatIso.naturality_2 e f

end NativeOmegaRecovery.FreeAdjunctionCoefficientSource

/-- Pasting the source and target comparison squares gives the square for
their composite comparisons. -/
theorem NativeOmegaRecovery.FreeFunctionCarrierComparison.pasting {D : Type*} [Category D]
    {H H' G G' K K' : D}
    {p : H ⟶ H'} {e : H ⟶ G} {e' : H' ⟶ G'} {b : G ⟶ G'}
    {τ : G ⟶ K} {τ' : G' ⟶ K'} {k : K ⟶ K'} {c : H ⟶ K} {c' : H' ⟶ K'}
    (hc : c = e ≫ τ) (hc' : c' = e' ≫ τ')
    (hs : p ≫ e' = e ≫ b) (ht : b ≫ τ' = τ ≫ k) : p ≫ c' = c ≫ k := by
  rw [hc, hc']
  calc
    _ = (p ≫ e') ≫ τ' := (Category.assoc p e' τ').symm
    _ = (e ≫ b) ≫ τ' := congrArg (fun z => z ≫ τ') hs
    _ = e ≫ (b ≫ τ') := Category.assoc e b τ'
    _ = e ≫ (τ ≫ k) := congrArg (fun z => e ≫ z) ht
    _ = _ := (Category.assoc e τ k).symm

/-- A forward comparison square gives the square through the inverse
isomorphisms. -/
theorem NativeOmegaRecovery.FreeFunctionCarrierComparison.sourceSquare {D : Type*} [Category D]
    {H H' G G' : D} (e : H ≅ G) (e' : H' ≅ G') (p : G ⟶ G') (q : H ⟶ H')
    (h : e.hom ≫ p = q ≫ e'.hom) : p ≫ e'.inv = e.inv ≫ q := by
  apply (cancel_mono e'.hom).1
  rw [Category.assoc, e'.inv_hom_id, Category.comp_id, Category.assoc, ← h,
    ← Category.assoc, e.inv_hom_id, Category.id_comp]

namespace NativeOmegaRecovery.FullFreeFunctionCoefficientTarget
universe uI vI uV vV
open scoped ExternalProduct
variable {I : Type uI} [Category.{vI} I] [MonoidalCategory I] [SymmetricCategory I]
  {V : Type uV} [Category.{vV} V] [MonoidalCategory V] [BraidedCategory V]
  [MonoidalClosed V] [∀ a b : I, HasCoproductsOfShape (a ⟶ b) V]
  [∀ (F G : I ⥤ V), (tensor I).HasPointwiseLeftKanExtension (F ⊠ G)]
  [(Functor.fromPUnit.{0} (𝟙_ I)).HasPointwiseLeftKanExtension
    (Functor.fromPUnit.{0} (𝟙_ V))]
  [∀ (v : V) (d : I), PreservesColimitsOfShape
    (CostructuredArrow (tensor I) d) (tensorLeft v)]
  [∀ (v : V) (d : I), PreservesColimitsOfShape
    (CostructuredArrow (tensor I) d) (tensorRight v)]
  [∀ (v : V) (d : I), PreservesColimitsOfShape
    (CostructuredArrow (Functor.fromPUnit.{0} (𝟙_ I)) d) (tensorLeft v)]
  [∀ (v : V) (d : I), PreservesColimitsOfShape
    (CostructuredArrow (Functor.fromPUnit.{0} (𝟙_ I)) d) (tensorRight v)]
  [∀ (v : V) (d : I × I), PreservesColimitsOfShape
    (CostructuredArrow ((𝟭 I).prod (Functor.fromPUnit.{0} (𝟙_ I))) d) (tensorRight v)]
  [∀ (v : V) (d : I × I), PreservesColimitsOfShape
    (CostructuredArrow ((tensor I).prod (𝟭 I)) d) (tensorRight v)]
  [∀ (F G : I ⥤ V) (c : I), HasEnd
    ((dayConvolutionInternalHomDiagramFunctor F).obj G |>.obj c)]
  [HasEqualizers (DayFunctor I V)]

variable [HasCoequalizers (DayFunctor I V)] (A : CommMon (DayFunctor I V))

/-- The full free-function comparison commutes with coefficient pre-maps
and a target transformation satisfying the given action and comparison squares. -/
theorem comparison_coefficient (r : I) {M' M : V} (f : M' ⟶ M)
    (K K' : Mod (DayFunctor I V) A.X ⥤ Mod (DayFunctor I V) A.X)
    (t : Mod.forget (D := DayFunctor I V) A.X ⋙
      NativeOmegaPreparation.DayIndexOrder.rightTargetFunctor r M ≅
        K ⋙ Mod.forget (D := DayFunctor I V) A.X)
    (t' : Mod.forget (D := DayFunctor I V) A.X ⋙
      NativeOmegaPreparation.DayIndexOrder.rightTargetFunctor r M' ≅
        K' ⋙ Mod.forget (D := DayFunctor I V) A.X)
    (hPair : ∀ N a n,
      NativeOmegaRecovery.FullFreeFunctionPair.targetAction A r M N a n ≫
        (t.app N).hom.natTrans.app (a ⊗ n) =
      (A.X.functor.obj a ◁ (t.app N).hom.natTrans.app n) ≫
        NativeOmegaRecovery.FullFreeFunctionModuleComparison.pairAction (A := A) (K.obj N) a n)
    (hPair' : ∀ N a n,
      NativeOmegaRecovery.FullFreeFunctionPair.targetAction A r M' N a n ≫
        (t'.app N).hom.natTrans.app (a ⊗ n) =
      (A.X.functor.obj a ◁ (t'.app N).hom.natTrans.app n) ≫
        NativeOmegaRecovery.FullFreeFunctionModuleComparison.pairAction (A := A) (K'.obj N) a n)
    (g : K ⟶ K')
    (ht : ∀ N : Mod (DayFunctor I V) A.X,
      PointedCGWH.Spectra.NativeStableMonoidal.DayFreeCoefficient.dayTargetScalarMap r f N.X ≫
        (t'.app N).hom = (t.app N).hom ≫ (g.app N).hom) :
    PointedCGWH.Spectra.NativeStableMonoidal.FreeModuleSource.pre A
        (PointedCGWH.Spectra.NativeStableMonoidal.DayFreeCoefficient.freeSequenceMap r f) ≫
      (NativeOmegaRecovery.FullFreeFunctionTargetNaturality.comparison
        A r M' K' t' hPair').hom =
    (NativeOmegaRecovery.FullFreeFunctionTargetNaturality.comparison
      A r M K t hPair).hom ≫ g := by
  apply NatTrans.ext
  funext N
  apply Mod.hom_ext
  let p :=
    ((PointedCGWH.Spectra.NativeStableMonoidal.FreeModuleSource.pre A
      (PointedCGWH.Spectra.NativeStableMonoidal.DayFreeCoefficient.freeSequenceMap r f)).app N).hom
  let e :=
    (NativeOmegaRecovery.FullFreeFunctionPair.comparison A r M N).hom
  let e' :=
    (NativeOmegaRecovery.FullFreeFunctionPair.comparison A r M' N).hom
  let b :=
    PointedCGWH.Spectra.NativeStableMonoidal.DayFreeCoefficient.dayTargetScalarMap r f N.X
  let τ := (t.app N).hom
  let τ' := (t'.app N).hom
  let k := (g.app N).hom
  let c :=
    ((NativeOmegaRecovery.FullFreeFunctionTargetNaturality.comparison
      A r M K t hPair).hom.app N).hom
  let c' :=
    ((NativeOmegaRecovery.FullFreeFunctionTargetNaturality.comparison
      A r M' K' t' hPair').hom.app N).hom
  have hc :=
    NativeOmegaRecovery.FullFreeFunctionTargetNaturality.hom_app_hom A r M K t hPair N
  have hc' :=
    NativeOmegaRecovery.FullFreeFunctionTargetNaturality.hom_app_hom A r M' K' t' hPair' N
  have hs :=
    PointedCGWH.Spectra.NativeStableMonoidal.DayFreeCoefficient.fullPair_coefficient A r f N
  have hTarget : b ≫ τ' = τ ≫ k := ht N
  change p ≫ c' = c ≫ k
  exact NativeOmegaRecovery.FreeFunctionCarrierComparison.pasting hc hc' hs hTarget

end NativeOmegaRecovery.FullFreeFunctionCoefficientTarget

namespace NativeOmegaRecovery.FreeFunctionCarrierComparison

universe uC vC uD vD
variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
  (E : C ≌ D) {F F' : C ⥤ C} {R R' : D ⥤ D}

/-- Carry a complete source comparison through the actual carrier counit. -/
def collapse (e : F ≅ E.functor ⋙ R ⋙ E.inverse) : F ⋙ E.functor ≅ E.functor ⋙ R :=
  Functor.isoWhiskerRight e E.functor ≪≫
    Functor.isoWhiskerLeft (E.functor ⋙ R) E.counitIso

/-- Actual source and target maps retain that same counit in the complete naturality square. -/
theorem collapse_coefficient (p : F ⟶ F') (q : R ⟶ R')
    (e : F ≅ E.functor ⋙ R ⋙ E.inverse)
    (e' : F' ≅ E.functor ⋙ R' ⋙ E.inverse)
    (h : p ≫ e'.hom = e.hom ≫
      Functor.whiskerLeft E.functor (Functor.whiskerRight q E.inverse)) :
    Functor.whiskerRight p E.functor ≫ (collapse E e').hom =
      (collapse E e).hom ≫ Functor.whiskerLeft E.functor q := by
  apply NatTrans.ext
  funext N
  let a := E.functor.map (e.hom.app N)
  let a' := E.functor.map (e'.hom.app N)
  let b := q.app (E.functor.obj N)
  let t := E.counitIso.hom.app (R.obj (E.functor.obj N))
  let t' := E.counitIso.hom.app (R'.obj (E.functor.obj N))
  let x := E.functor.map (E.inverse.map b)
  have hp := congrArg (fun z => E.functor.map (z.app N)) h
  simp only [NatTrans.comp_app, Functor.map_comp] at hp
  change E.functor.map (p.app N) ≫ a' = a ≫ x at hp
  have ht := E.counitIso.hom.naturality b
  change x ≫ t' = t ≫ b at ht
  change E.functor.map (p.app N) ≫ (a' ≫ t') = (a ≫ t) ≫ b
  exact NativeOmegaRecovery.FreeFunctionCarrierComparison.pasting rfl rfl hp ht

end NativeOmegaRecovery.FreeFunctionCarrierComparison

namespace NativeOmegaRecovery.NativeSymmetricFreeFunction

private abbrev I := Operad.SmallFinBijGroupoid
private abbrev V := PointedCGWH.{u, v}
private abbrev Sequence := PointedCGWH.SymmetricSequence.{u, v}
private abbrev S := PointedCGWH.sphereSequence.{u, v}
private abbrev A := PointedCGWH.sphereSequenceCommMon.{u, v}
private abbrev Carrier :=
  EnrichedFunctorCat V.{u, v} PointedCGWH.SymmetricOperatorIndex.{u, v}

attribute [local instance] Operad.SmallFinBijGroupoid.instMonoidalCategory
  Operad.SmallFinBijGroupoid.instSymmetricCategory
  PointedCGWH.copowerUnderlyingEnrichedOrdinary PointedCGWH.copowerUnderlyingMonoidal
  PointedCGWH.sphereSequenceMonObj PointedCGWH.sphereSequenceIsCommMonObj
  PointedCGWH.EnrichedMapping.hasSmallLimits
  NativeOmegaPreparation.SymmetricFunction.sequenceCoequalizers
  NativeOmegaPreparation.SymmetricFunction.sequenceEqualizers
  PointedCGWH.originalSymmetricSequenceMonoidal
  PointedCGWH.originalSymmetricSequenceBraided PointedCGWH.originalSymmetricSequenceSymmetric
  NativeOmegaPreparation.SymmetricFunction.sequenceClosed

open NativeOmegaRecovery.NativeSymmetricFreeSource
open PointedCGWH.SymmetricModulePresentation

/-- The actual original comparison source retains the complete internal-Hom
functor and both original carrier functors. -/
theorem comparison_source (r : I) (M : V.{u, v}) :
    NativeOmegaPreparation.SymmetricFunction.functor r M =
      operatorToModule ⋙
        Mod.internalHom A.{u, v} ((Mod.dayFreeAt S.{u, v} r).obj M) ⋙
        moduleToOperator :=
  NativeOmegaPreparation.ModuleFunctionTransport.sourceFunctor_obj A.{u, v}
    moduleOperatorEquivalence.{u, v} ((Mod.dayFreeAt S.{u, v} r).obj M)

/-- The native free-source transport of a coefficient arrow is the original
free Day-module map. -/
theorem sourceArrow_coefficient (r : I) {M' M : V.{u, v}} (f : M' ⟶ M) :
    sourceArrow.{u, v} (r := r) (s := r) (M := M) (M' := M')
        (Free.coefficientMap (V := V.{u, v}) (X := M') (Y := M)
          (PointedCGWH.symmetricOperatorObj.{u, v} r) f) =
      (Mod.dayFreeAt S.{u, v} r).map f := by
  exact NativeOmegaRecovery.FreeAdjunctionCoefficientSource.sourceArrow_coefficient
    A.{u, v} moduleOperatorEquivalence.{u, v}
    (PointedCGWH.symmetricOperatorObj.{u, v} r) (Mod.dayFreeAt S.{u, v} r)
    (NativeOmegaPreparation.SymmetricNativeFree.comparison.{u, v} r) f

/-- Every coefficient arrow induces the original full contravariant cotensor transformation. -/
abbrev cotensorSourceNat {M' M : V.{u, v}} (f : M' ⟶ M) :
    cotensor (I := PointedCGWH.SymmetricOperatorIndex.{u, v}) M ⟶ cotensor M' :=
  (ScalarLeibniz.cotensorBifunctor
    (V := V.{u, v}) (A := PointedCGWH.SymmetricOperatorIndex.{u, v})).map f.op

/-- Each original cotensor coefficient component is the scalar internal-Hom pre-map. -/
theorem cotensorSourceNat_component {M' M : V.{u, v}} (f : M' ⟶ M)
    (E : Carrier.{u, v}) (n : I) :
    component ((cotensorSourceNat f).app E) (PointedCGWH.symmetricOperatorObj.{u, v} n) =
      (MonoidalClosed.pre f).app
        (E.toEnrichedFunctor.obj (PointedCGWH.symmetricOperatorObj.{u, v} n)) :=
  cotensorScalarMap_component f E (PointedCGWH.symmetricOperatorObj.{u, v} n)

/-- The actual carrier functors transport that cotensor transformation through the native shift. -/
def targetModuleSourceNat (r : I) {M' M : V.{u, v}} (f : M' ⟶ M) :
    NativeOmegaRecovery.NativeSymmetricFreeFunction.targetModuleFunctor.{u, v} r M ⟶
      NativeOmegaRecovery.NativeSymmetricFreeFunction.targetModuleFunctor.{u, v} r M' :=
  Functor.whiskerLeft (moduleToOperator.{u, v} ⋙ PointedCGWH.SymmetricShift.functor.{u, v} r)
    (Functor.whiskerRight (cotensorSourceNat f) operatorToModule.{u, v})

/-- Each target-module coefficient component is precomposition in the original
shifted scalar internal Hom. -/
theorem targetModuleSourceNat_component (r : I) {M' M : V.{u, v}} (f : M' ⟶ M)
    (N : Mod Sequence.{u, v} S.{u, v}) (n : I) :
    ((targetModuleSourceNat r f).app N).hom.natTrans.app n =
      (MonoidalClosed.pre f).app (N.X.functor.obj (n ⊗ r)) := by
  let g := cotensorScalarMap f
    ((PointedCGWH.SymmetricShift.functor.{u, v} r).obj (moduleToOperator.{u, v}.obj N))
  have hK := congrArg (fun z => z.natTrans.app n) (reconstructedModuleMap_hom g)
  have hR := PointedCGWH.symmetricSequenceRestriction_component g n
  have hS := cotensorScalarMap_component f
    ((PointedCGWH.SymmetricShift.functor.{u, v} r).obj (moduleToOperator.{u, v}.obj N))
    (PointedCGWH.symmetricOperatorObj.{u, v} n)
  exact hK.trans (hR.trans hS)


/-- The original target-sequence comparison intertwines scalar coefficient
precomposition and the target-module transformation. -/
theorem targetSequenceSource_square (r : I) {M' M : V.{u, v}} (f : M' ⟶ M)
    (N : Mod Sequence.{u, v} S.{u, v}) :
    PointedCGWH.Spectra.NativeStableMonoidal.DayFreeCoefficient.dayTargetScalarMap r f N.X ≫
        (NativeOmegaRecovery.NativeSymmetricFreeFunction.targetSequenceNatIso.{u, v}
          r M').hom.app N =
      (NativeOmegaRecovery.NativeSymmetricFreeFunction.targetSequenceNatIso.{u, v}
        r M).hom.app N ≫ ((targetModuleSourceNat r f).app N).hom := by
  apply DayFunctor.hom_ext
  apply NatTrans.ext
  funext n
  let X := (ihom M).obj (N.X.functor.obj (n ⊗ r))
  let Y := (ihom M').obj (N.X.functor.obj (n ⊗ r))
  let b : X ⟶ Y := (MonoidalClosed.pre f).app (N.X.functor.obj (n ⊗ r))
  let k : X ⟶ Y := ((targetModuleSourceNat r f).app N).hom.natTrans.app n
  let τ : X ⟶ X := (NativeOmegaRecovery.NativeSymmetricFreeFunction.targetSequenceNatIso.{u, v}
    r M).hom.app N |>.natTrans.app n
  let τ' : Y ⟶ Y := (NativeOmegaRecovery.NativeSymmetricFreeFunction.targetSequenceNatIso.{u, v}
    r M').hom.app N |>.natTrans.app n
  have hτ := NativeOmegaRecovery.NativeSymmetricFreeFunction.targetSequenceIso_inv_component
    r M N n
  have hτ' := NativeOmegaRecovery.NativeSymmetricFreeFunction.targetSequenceIso_inv_component
    r M' N n
  have hk := targetModuleSourceNat_component r f N n
  change b ≫ τ' = τ ≫ k
  change τ = 𝟙 X at hτ
  change τ' = 𝟙 Y at hτ'
  change k = b at hk
  rw [hτ, hτ', Category.comp_id, Category.id_comp]
  exact hk.symm


/-- The full original module comparison intertwines the free-module coefficient
pre-map and its shifted cotensor target transformation. -/
theorem moduleComparisonNat_coefficient (r : I) {M' M : V.{u, v}} (f : M' ⟶ M) :
    PointedCGWH.Spectra.NativeStableMonoidal.FreeModuleSource.pre A.{u, v}
        (PointedCGWH.Spectra.NativeStableMonoidal.DayFreeCoefficient.freeSequenceMap r f) ≫
      (NativeOmegaRecovery.NativeSymmetricFreeFunction.moduleComparisonNat.{u, v} r M').hom =
    (NativeOmegaRecovery.NativeSymmetricFreeFunction.moduleComparisonNat.{u, v} r M).hom ≫
      targetModuleSourceNat r f :=
  NativeOmegaRecovery.FullFreeFunctionCoefficientTarget.comparison_coefficient A.{u, v} r f
    (NativeOmegaRecovery.NativeSymmetricFreeFunction.targetModuleFunctor r M)
    (NativeOmegaRecovery.NativeSymmetricFreeFunction.targetModuleFunctor r M')
    (NativeOmegaRecovery.NativeSymmetricFreeFunction.targetSequenceNatIso r M)
    (NativeOmegaRecovery.NativeSymmetricFreeFunction.targetSequenceNatIso r M')
    (NativeOmegaRecovery.NativeSymmetricFreeFunction.native_target_pair_square r M)
    (NativeOmegaRecovery.NativeSymmetricFreeFunction.native_target_pair_square r M')
    (targetModuleSourceNat r f) (targetSequenceSource_square r f)



/-- The original whole operator comparison is precisely its actual complete carrier-counit collapse. -/
theorem moduleOperatorComparison_collapse (r : I) (M : V.{u, v}) :
    moduleOperatorComparison.{u, v} r M =
      FreeFunctionCarrierComparison.collapse moduleOperatorEquivalence.{u, v}
        (moduleComparisonNat.{u, v} r M) := rfl

end NativeOmegaRecovery.NativeSymmetricFreeFunction

namespace NativeOmegaRecovery.FullFreeFunctionCoefficientTarget

universe uI vI uV vV
open scoped ExternalProduct

variable {I : Type uI} [Category.{vI} I] [MonoidalCategory I] [SymmetricCategory I]
  {V : Type uV} [Category.{vV} V] [MonoidalCategory V] [BraidedCategory V]
  [MonoidalClosed V] [∀ a b : I, HasCoproductsOfShape (a ⟶ b) V]
  [∀ (F G : I ⥤ V), (tensor I).HasPointwiseLeftKanExtension (F ⊠ G)]
  [(Functor.fromPUnit.{0} (𝟙_ I)).HasPointwiseLeftKanExtension
    (Functor.fromPUnit.{0} (𝟙_ V))]
  [∀ (v : V) (d : I), PreservesColimitsOfShape
    (CostructuredArrow (tensor I) d) (tensorLeft v)]
  [∀ (v : V) (d : I), PreservesColimitsOfShape
    (CostructuredArrow (tensor I) d) (tensorRight v)]
  [∀ (v : V) (d : I), PreservesColimitsOfShape
    (CostructuredArrow (Functor.fromPUnit.{0} (𝟙_ I)) d) (tensorLeft v)]
  [∀ (v : V) (d : I), PreservesColimitsOfShape
    (CostructuredArrow (Functor.fromPUnit.{0} (𝟙_ I)) d) (tensorRight v)]
  [∀ (v : V) (d : I × I), PreservesColimitsOfShape
    (CostructuredArrow ((𝟭 I).prod (Functor.fromPUnit.{0} (𝟙_ I))) d) (tensorRight v)]
  [∀ (v : V) (d : I × I), PreservesColimitsOfShape
    (CostructuredArrow ((tensor I).prod (𝟭 I)) d) (tensorRight v)]
  [∀ (F G : I ⥤ V) (c : I), HasEnd
    ((dayConvolutionInternalHomDiagramFunctor F).obj G |>.obj c)]
  [HasEqualizers (DayFunctor I V)] [HasCoequalizers (DayFunctor I V)]
  (A : CommMon (DayFunctor I V))

attribute [local irreducible] Mod.internalHom

/-- At each actual target module, the full free-function comparison retains
the original free-module pre-map, both pair-action laws, both target-sequence
isomorphisms, and the given entire module target transformation. -/
theorem comparison_coefficient_app (r : I) {M' M : V} (f : M' ⟶ M)
    (K K' : Mod (DayFunctor I V) A.X ⥤ Mod (DayFunctor I V) A.X)
    (t : Mod.forget (D := DayFunctor I V) A.X ⋙
      NativeOmegaPreparation.DayIndexOrder.rightTargetFunctor r M ≅
        K ⋙ Mod.forget (D := DayFunctor I V) A.X)
    (t' : Mod.forget (D := DayFunctor I V) A.X ⋙
      NativeOmegaPreparation.DayIndexOrder.rightTargetFunctor r M' ≅
        K' ⋙ Mod.forget (D := DayFunctor I V) A.X)
    (hPair : ∀ N a n,
      NativeOmegaRecovery.FullFreeFunctionPair.targetAction A r M N a n ≫
        (t.app N).hom.natTrans.app (a ⊗ n) =
      (A.X.functor.obj a ◁ (t.app N).hom.natTrans.app n) ≫
        NativeOmegaRecovery.FullFreeFunctionModuleComparison.pairAction (A := A) (K.obj N) a n)
    (hPair' : ∀ N a n,
      NativeOmegaRecovery.FullFreeFunctionPair.targetAction A r M' N a n ≫
        (t'.app N).hom.natTrans.app (a ⊗ n) =
      (A.X.functor.obj a ◁ (t'.app N).hom.natTrans.app n) ≫
        NativeOmegaRecovery.FullFreeFunctionModuleComparison.pairAction (A := A) (K'.obj N) a n)
    (g : K ⟶ K')
    (ht : ∀ N : Mod (DayFunctor I V) A.X,
      PointedCGWH.Spectra.NativeStableMonoidal.DayFreeCoefficient.dayTargetScalarMap r f N.X ≫
        (t'.app N).hom = (t.app N).hom ≫ (g.app N).hom)
    (N : Mod (DayFunctor I V) A.X) :
    (PointedCGWH.Spectra.NativeStableMonoidal.FreeModuleSource.pre A
        (PointedCGWH.Spectra.NativeStableMonoidal.DayFreeCoefficient.freeSequenceMap r f) ≫
      (NativeOmegaRecovery.FullFreeFunctionTargetNaturality.comparison
        A r M' K' t' hPair').hom).app N =
    ((NativeOmegaRecovery.FullFreeFunctionTargetNaturality.comparison
      A r M K t hPair).hom ≫ g).app N := by
  apply Mod.hom_ext
  let p :=
    ((PointedCGWH.Spectra.NativeStableMonoidal.FreeModuleSource.pre A
      (PointedCGWH.Spectra.NativeStableMonoidal.DayFreeCoefficient.freeSequenceMap r f)).app N).hom
  let e := (NativeOmegaRecovery.FullFreeFunctionPair.comparison A r M N).hom
  let e' := (NativeOmegaRecovery.FullFreeFunctionPair.comparison A r M' N).hom
  let b :=
    PointedCGWH.Spectra.NativeStableMonoidal.DayFreeCoefficient.dayTargetScalarMap r f N.X
  let τ := (t.app N).hom
  let τ' := (t'.app N).hom
  let k := (g.app N).hom
  let c :=
    ((NativeOmegaRecovery.FullFreeFunctionTargetNaturality.comparison
      A r M K t hPair).hom.app N).hom
  let c' :=
    ((NativeOmegaRecovery.FullFreeFunctionTargetNaturality.comparison
      A r M' K' t' hPair').hom.app N).hom
  have hc :=
    NativeOmegaRecovery.FullFreeFunctionTargetNaturality.hom_app_hom A r M K t hPair N
  have hc' :=
    NativeOmegaRecovery.FullFreeFunctionTargetNaturality.hom_app_hom A r M' K' t' hPair' N
  have hs :=
    PointedCGWH.Spectra.NativeStableMonoidal.DayFreeCoefficient.fullPair_coefficient A r f N
  have hTarget : b ≫ τ' = τ ≫ k := ht N
  change p ≫ c' = c ≫ k
  exact NativeOmegaRecovery.FreeFunctionCarrierComparison.pasting hc hc' hs hTarget

/-- Every literal level of the same full coefficient comparison retains
the original free-module pre-map, both complete target comparisons and
the actual target module component, before native source specialization. -/
theorem comparison_coefficient_app_level (r : I) {M' M : V} (f : M' ⟶ M)
    (K K' : Mod (DayFunctor I V) A.X ⥤ Mod (DayFunctor I V) A.X)
    (t : Mod.forget (D := DayFunctor I V) A.X ⋙
      NativeOmegaPreparation.DayIndexOrder.rightTargetFunctor r M ≅
        K ⋙ Mod.forget (D := DayFunctor I V) A.X)
    (t' : Mod.forget (D := DayFunctor I V) A.X ⋙
      NativeOmegaPreparation.DayIndexOrder.rightTargetFunctor r M' ≅
        K' ⋙ Mod.forget (D := DayFunctor I V) A.X)
    (hPair : ∀ N a n,
      NativeOmegaRecovery.FullFreeFunctionPair.targetAction A r M N a n ≫
        (t.app N).hom.natTrans.app (a ⊗ n) =
      (A.X.functor.obj a ◁ (t.app N).hom.natTrans.app n) ≫
        NativeOmegaRecovery.FullFreeFunctionModuleComparison.pairAction (A := A) (K.obj N) a n)
    (hPair' : ∀ N a n,
      NativeOmegaRecovery.FullFreeFunctionPair.targetAction A r M' N a n ≫
        (t'.app N).hom.natTrans.app (a ⊗ n) =
      (A.X.functor.obj a ◁ (t'.app N).hom.natTrans.app n) ≫
        NativeOmegaRecovery.FullFreeFunctionModuleComparison.pairAction (A := A) (K'.obj N) a n)
    (g : K ⟶ K')
    (ht : ∀ N : Mod (DayFunctor I V) A.X,
      PointedCGWH.Spectra.NativeStableMonoidal.DayFreeCoefficient.dayTargetScalarMap r f N.X ≫
        (t'.app N).hom = (t.app N).hom ≫ (g.app N).hom)
    (N : Mod (DayFunctor I V) A.X) (n : I) :
    ((PointedCGWH.Spectra.NativeStableMonoidal.FreeModuleSource.pre A
        (PointedCGWH.Spectra.NativeStableMonoidal.DayFreeCoefficient.freeSequenceMap r f)).app N).hom.natTrans.app n ≫
      ((NativeOmegaRecovery.FullFreeFunctionTargetNaturality.comparison
        A r M' K' t' hPair').hom.app N).hom.natTrans.app n =
    ((NativeOmegaRecovery.FullFreeFunctionTargetNaturality.comparison
      A r M K t hPair).hom.app N).hom.natTrans.app n ≫
        (g.app N).hom.natTrans.app n := by
  let p := PointedCGWH.Spectra.NativeStableMonoidal.FreeModuleSource.pre A
    (PointedCGWH.Spectra.NativeStableMonoidal.DayFreeCoefficient.freeSequenceMap r f)
  let e := NativeOmegaRecovery.FullFreeFunctionTargetNaturality.comparison
    A r M K t hPair
  let e' := NativeOmegaRecovery.FullFreeFunctionTargetNaturality.comparison
    A r M' K' t' hPair'
  have h : p.app N ≫ e'.hom.app N = e.hom.app N ≫ g.app N :=
    comparison_coefficient_app A r f K K' t t' hPair hPair' g ht N
  let ev := Mod.dayEvaluation A.X n
  have hv := congrArg (fun k => ev.map k) h
  exact (ev.map_comp (p.app N) (e'.hom.app N)).symm.trans
    (hv.trans (ev.map_comp (e.hom.app N) (g.app N)))

end NativeOmegaRecovery.FullFreeFunctionCoefficientTarget


set_option autoImplicit false
noncomputable section

open CategoryTheory MonoidalCategory
open CategoryTheory.EnrichedFunctorCat
open scoped MonoidalClosed CategoryTheory.MonObj

namespace NativeOmegaRecovery.NativeScalarCoefficient

private abbrev I := Operad.SmallFinBijGroupoid
private abbrev V := PointedCGWH.{u, v}
private abbrev A := PointedCGWH.sphereSequenceCommMon.{u, v}
private abbrev Sequence := PointedCGWH.SymmetricSequence.{u, v}

attribute [local instance] Operad.SmallFinBijGroupoid.instMonoidalCategory
  Operad.SmallFinBijGroupoid.instSymmetricCategory
  PointedCGWH.copowerUnderlyingEnrichedOrdinary PointedCGWH.copowerUnderlyingMonoidal
  PointedCGWH.sphereSequenceMonObj PointedCGWH.sphereSequenceIsCommMonObj
  PointedCGWH.EnrichedMapping.hasSmallLimits
  NativeOmegaPreparation.SymmetricFunction.sequenceCoequalizers
  NativeOmegaPreparation.SymmetricFunction.sequenceEqualizers
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
open NativeOmegaRecovery.NativeSymmetricFreeFunction
open PointedCGWH.Spectra.NativeStableMonoidal

/-- The named original factories retain the full selected Day monoidal data. -/
theorem factoryMonoidal_eq_original : PointedCGWH.SymmetricFunctionFactories.monoidal.{u, v} =
    PointedCGWH.originalSymmetricSequenceMonoidal.{u, v} :=
  PointedCGWH.SymmetricFunctionFactories.monoidal_eq_original

/-- Every right adjoint, unit, counit and triangle belongs to the same selected closed record. -/
theorem factorySequenceClosed_eq_original :
    (inferInstance : @MonoidalClosed Sequence.{u, v} _
      PointedCGWH.SymmetricFunctionFactories.monoidal.{u, v}) =
    NativeOmegaPreparation.SymmetricFunction.sequenceClosed.{u, v} := rfl

/-- The commutative sphere coefficient retains the entire original sphere sequence. -/
theorem sphereCoefficient_obj_eq : A.{u, v}.X = PointedCGWH.sphereSequence.{u, v} := rfl

/-- Its complete unit and multiplication data are the selected native sphere monoid. -/
theorem sphereCoefficient_mon_eq : A.{u, v}.mon = PointedCGWH.sphereSequenceMonObj.{u, v} := rfl

attribute [local instance] NativeOmegaPreparation.SymmetricFunction.sequenceClosed
  PointedCGWH.originalSymmetricSequenceMonoidal
  PointedCGWH.originalSymmetricSequenceBraided
  PointedCGWH.originalSymmetricSequenceSymmetric

/-- The actual source object of the original free-module coefficient pre-map. -/
abbrev coefficientSourceModule (r : I) (M : V.{u, v}) (N : OriginalModule.{u, v}) :
    OriginalModule.{u, v} :=
  (Mod.internalHom A.{u, v}
    ((Mod.free A.{u, v}.X).obj (DayFreeCoefficient.freeSequence r M))).obj N

/-- The existing original-Hom equality retains the complete coefficient source module. -/
theorem originalHom_eq_coefficientSourceModule (r : I) (M : V.{u, v})
    (N : OriginalModule.{u, v}) :
    originalHom r M N = coefficientSourceModule r M N := by
  have h := originalHom_eq_originalInternalHom r M N
  refine h.trans ?_
  dsimp only [coefficientSourceModule, DayFreeCoefficient.freeSequence]
  rw [← factorySequenceClosed_eq_original]
  congr 4

/-- Both whole module objects are transported by the existing original source equality. -/
def originalHomCoefficientIso (r : I) (M : V.{u, v}) (N : OriginalModule.{u, v}) :
    originalHom r M N ≅ coefficientSourceModule r M N :=
  eqToIso (originalHom_eq_coefficientSourceModule r M N)


universe uC vC

private theorem transportedArrow_back {C : Type uC} [Category.{vC} C]
    {H H' G G' : C} (e : H ≅ G) (e' : H' ≅ G') (p : G ⟶ G') :
    e.inv ≫ (e.hom ≫ p ≫ e'.inv) ≫ e'.hom = p := by
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]

/-- The actual original coefficient pre-map, with its two given module objects. -/
def coefficientPreArrow (r : I) {M' M : V.{u, v}} (f : M' ⟶ M)
    (N : OriginalModule.{u, v}) :=
  Arrow.mk ((FreeModuleSource.pre A.{u, v}
    (DayFreeCoefficient.freeSequenceMap r f)).app N)

/-- The whole source object of that actual pre-map is the given coefficient source. -/
theorem coefficientPreArrow_left (r : I) {M' M : V.{u, v}} (f : M' ⟶ M)
    (N : OriginalModule.{u, v}) :
    (coefficientPreArrow r f N).left = coefficientSourceModule r M N := by
  dsimp only [coefficientPreArrow, Arrow.mk_left, coefficientSourceModule]

/-- Its whole target object retains the independent source coefficient. -/
theorem coefficientPreArrow_right (r : I) {M' M : V.{u, v}} (f : M' ⟶ M)
    (N : OriginalModule.{u, v}) :
    (coefficientPreArrow r f N).right = coefficientSourceModule r M' N := by
  dsimp only [coefficientPreArrow, Arrow.mk_right, coefficientSourceModule]

/-- The original Hom is transported to the actual source of the given pre-map. -/
def originalToPreLeftIso (r : I) {M' M : V.{u, v}} (f : M' ⟶ M)
    (N : OriginalModule.{u, v}) : originalHom r M N ≅ (coefficientPreArrow r f N).left :=
  originalHomCoefficientIso r M N ≪≫ eqToIso (coefficientPreArrow_left r f N).symm

/-- The independent original Hom is transported to the actual target of the same map. -/
def originalToPreRightIso (r : I) {M' M : V.{u, v}} (f : M' ⟶ M)
    (N : OriginalModule.{u, v}) : originalHom r M' N ≅ (coefficientPreArrow r f N).right :=
  originalHomCoefficientIso r M' N ≪≫ eqToIso (coefficientPreArrow_right r f N).symm

/-- Both original object transports carry the entire literal coefficient pre-map. -/
def originalCoefficientModuleMap (r : I) {M' M : V.{u, v}} (f : M' ⟶ M)
    (N : OriginalModule.{u, v}) : originalHom r M N ⟶ originalHom r M' N :=
  (originalToPreLeftIso r f N).hom ≫ (coefficientPreArrow r f N).hom ≫
    (originalToPreRightIso r f N).inv

/-- Returning through those same two transports recovers the whole given arrow. -/
theorem originalCoefficientModuleMap_back (r : I) {M' M : V.{u, v}} (f : M' ⟶ M)
    (N : OriginalModule.{u, v}) :
    (originalToPreLeftIso r f N).inv ≫ originalCoefficientModuleMap r f N ≫
        (originalToPreRightIso r f N).hom = (coefficientPreArrow r f N).hom := by
  dsimp only [originalCoefficientModuleMap]
  exact transportedArrow_back (originalToPreLeftIso r f N) (originalToPreRightIso r f N)
    (coefficientPreArrow r f N).hom

end NativeOmegaRecovery.NativeScalarCoefficient
