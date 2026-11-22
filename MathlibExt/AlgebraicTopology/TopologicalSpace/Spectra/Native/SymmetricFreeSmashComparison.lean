/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.StableMonoidalAssembly
import MathlibExt.CategoryTheory.Monoidal.Mod.FreePairRelativeTensor
import MathlibExt.CategoryTheory.Monoidal.DayConvolution.FinBijRepresentablePair
import MathlibExt.AlgebraicTopology.Spectra.Symmetric.PointedCGWH.FunctionSpectrum.NativeFreeSourceComparison
import MathlibExt.CategoryTheory.Monoidal.Transport.PairFreeSource

/-!
# Full coefficient comparisons for native symmetric free smash

The actual balanced free smash is compared with the scalar tensor and the
original enriched right-block left Kan extension. Both original adjunction
units and counits and the full coefficient maps remain part of the API.
-/

set_option autoImplicit false
noncomputable section
universe u v

open CategoryTheory MonoidalCategory HomotopicalAlgebra
open CategoryTheory.EnrichedFunctorCat
open HomotopicalAlgebra.EnrichedProjective.Native
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK
open scoped MonoidalClosed CGWH.modelCategory CategoryTheory.MonObj

/-!
## Coefficient maps and literal native free-smash comparisons

The original module free-unit and Day end projections retain every whole
coefficient arrow. The native free smash comparison uses the existing full
free-function adjunction, the actual scalar/free associator and the genuine
right-block coend Lan. Its target has the original ordered index `s ⊗ r`.
These comparisons do not assert a pushout-product or stable model axiom.
-/

open scoped ExternalProduct CGWH.limits
open CategoryTheory.Limits
universe uI vI uV vV

namespace PointedCGWH.Spectra.NativeStableMonoidal.FreeModuleSource
universe uC vC
variable {C : Type uC} [Category.{vC} C] [MonoidalCategory C] [BraidedCategory C]
  [MonoidalClosed C] [HasEqualizers C] [HasCoequalizers C] (A : CommMon C)
/-- The original balanced monoidal structure on modules over the commutative scalar. -/
local instance originalModuleMonoidal : MonoidalCategory (Mod C A.X) :=
  Mod.instMonoidalCategory A
/-- The original internal-Hom closed structure on modules over the commutative scalar. -/
local instance originalModuleClosed : MonoidalClosed (Mod C A.X) :=
  Mod.instMonoidalClosed A

/-- The unchanged original free-module pre-map, named before specializing the ambient carrier. -/
def pre {P P' : C} (f : P' ⟶ P) :
    Mod.internalHom A ((Mod.free A.X).obj P) ⟶
      Mod.internalHom A ((Mod.free A.X).obj P') :=
  MonoidalClosed.pre ((Mod.free A.X).map f)

/-- This is a whole-value equality with the given original balanced source pre-map. -/
theorem pre_eq_original {P P' : C} (f : P' ⟶ P) :
    pre A f = MonoidalClosed.pre ((Mod.free A.X).map f) := rfl

/-- The same original free-unit evaluation retains every whole source coefficient arrow. -/
theorem pre_forward {P P' : C} (f : P' ⟶ P) (N : Mod C A.X) :
    ((pre A f).app N).hom ≫ Mod.FreeInternalHom.forward A P' N =
      Mod.FreeInternalHom.forward A P N ≫ (MonoidalClosed.pre f).app N.X :=
  Mod.FreeInternalHom.forward_free_map A f N

end PointedCGWH.Spectra.NativeStableMonoidal.FreeModuleSource

namespace PointedCGWH.Spectra.NativeStableMonoidal.DayFreeCoefficient

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

/-- The original representable Day sequence at an arbitrary index and coefficient. -/
def freeSequence (r : I) (M : V) : DayFunctor I V :=
  .mk ((evaluationLeftAdjoint V r).obj M)

/-- The representable Day sequence map induced by the complete coefficient arrow. -/
def freeSequenceMap (r : I) {M' M : V} (f : M' ⟶ M) :
    freeSequence r M' ⟶ freeSequence r M :=
  (DayFunctor.equiv I V).inverse.map ((evaluationLeftAdjoint V r).map f)

/-- The original end and block-braiding comparison of the complete Day free-source function. -/
def dayTargetComparison (r : I) (M : V) (G : DayFunctor I V) :
    (DayFunctor.internalHom (freeSequence r M)).obj G ≅
      (NativeOmegaPreparation.DayIndexOrder.rightTargetFunctor r M).obj G :=
  (NativeOmegaPreparation.DayFreeEnd.comparison r M ≪≫
    NativeOmegaPreparation.DayIndexOrder.comparison r M).app G

/-- The actual closed coefficient pre-map on every original right-shifted target. -/
def dayTargetScalarMap (r : I) {M' M : V} (f : M' ⟶ M) (G : DayFunctor I V) :
    (NativeOmegaPreparation.DayIndexOrder.rightTargetFunctor r M).obj G ⟶
      (NativeOmegaPreparation.DayIndexOrder.rightTargetFunctor r M').obj G :=
  (DayFunctor.equiv I V).inverse.map
    (Functor.whiskerLeft (MonoidalCategory.tensorRight r ⋙ G.functor) (MonoidalClosed.pre f))

omit [HasEqualizers (DayFunctor I V)] in
set_option backward.isDefEq.respectTransparency false in
/-- The full free-function comparison retains arbitrary coefficient arrows
and the actual block map. -/
theorem dayTargetComparison_coefficient (r : I) {M' M : V} (f : M' ⟶ M)
    (G : DayFunctor I V) :
    (MonoidalClosed.pre (freeSequenceMap r f)).app G ≫
        (dayTargetComparison r M' G).hom =
      (dayTargetComparison r M G).hom ≫ dayTargetScalarMap r f G := by
  apply DayFunctor.hom_ext
  apply NatTrans.ext
  funext n
  let T := G.functor.obj (r ⊗ n)
  let T' := G.functor.obj (n ⊗ r)
  let g : M ⟶ (freeSequence r M).functor.obj r :=
    Sigma.ι (fun _ : r ⟶ r => M) (𝟙 r)
  let g' : M' ⟶ (freeSequence r M').functor.obj r :=
    Sigma.ι (fun _ : r ⟶ r => M') (𝟙 r)
  let H : V := ((DayFunctor.internalHom (freeSequence r M)).obj G).functor.obj n
  let πr : H ⟶ (ihom ((freeSequence r M).functor.obj r)).obj T := end_.π
    ((dayConvolutionInternalHomDiagramFunctor (freeSequence r M).functor).obj
      G.functor |>.obj n) r
  let b := G.functor.map (β_ r n).hom
  have hg : g' ≫ (freeSequenceMap r f).natTrans.app r = f ≫ g := by
    change Sigma.ι (fun _ : r ⟶ r => M') (𝟙 r) ≫
      Sigma.desc (fun h : r ⟶ r => f ≫ Sigma.ι (fun _ : r ⟶ r => M) h) = _
    exact Sigma.ι_comp_desc _ _
  have hp := NativeOmegaRecovery.FullFreeFunctionNaturality.day_free_source_projection
    r r M M' (freeSequenceMap r f) G n
  change ((MonoidalClosed.pre (freeSequenceMap r f)).app G).natTrans.app n ≫
      (dayTargetComparison r M' G).hom.natTrans.app n =
    πr ≫ (MonoidalClosed.pre (g' ≫ (freeSequenceMap r f).natTrans.app r)).app T ≫
      (ihom M').map b at hp
  rw [hg] at hp
  have hpre : (MonoidalClosed.pre (f ≫ g)).app T =
      (MonoidalClosed.pre g).app T ≫ (MonoidalClosed.pre f).app T := by
    exact congrArg (fun q => q.app T) (MonoidalClosed.pre_map f g)
  have he : (dayTargetComparison r M G).hom.natTrans.app n =
      πr ≫ (MonoidalClosed.pre g).app T ≫ (ihom M).map b := by
    have h := NativeOmegaRecovery.FullFreeFunctionNaturality.day_free_source_projection
      r r M M (𝟙 (freeSequence r M)) G n
    change ((MonoidalClosed.pre (𝟙 (freeSequence r M))).app G).natTrans.app n ≫
        (dayTargetComparison r M G).hom.natTrans.app n =
      πr ≫ (MonoidalClosed.pre (g ≫ 𝟙 ((freeSequence r M).functor.obj r))).app T ≫
        (ihom M).map b at h
    simpa only [MonoidalClosed.pre_id, NatTrans.id_app, DayFunctor.id_natTrans,
      Category.id_comp, Category.comp_id] using h
  change ((MonoidalClosed.pre (freeSequenceMap r f)).app G).natTrans.app n ≫
      (dayTargetComparison r M' G).hom.natTrans.app n =
    (dayTargetComparison r M G).hom.natTrans.app n ≫ (MonoidalClosed.pre f).app T'
  rw [hp, hpre, he]
  calc
    πr ≫ ((MonoidalClosed.pre g).app T ≫ (MonoidalClosed.pre f).app T) ≫ (ihom M').map b =
        πr ≫ (MonoidalClosed.pre g).app T ≫
          ((MonoidalClosed.pre f).app T ≫ (ihom M').map b) := by
            exact congrArg (fun q => πr ≫ q) (Category.assoc _ _ _)
    _ = πr ≫ (MonoidalClosed.pre g).app T ≫
          ((ihom M).map b ≫ (MonoidalClosed.pre f).app T') :=
        congrArg (fun q => πr ≫ (MonoidalClosed.pre g).app T ≫ q)
          ((MonoidalClosed.pre f).naturality b).symm
    _ = _ := (congrArg (fun q => πr ≫ q) (Category.assoc
      ((MonoidalClosed.pre g).app T) ((ihom M).map b)
        ((MonoidalClosed.pre f).app T')).symm).trans
      (Category.assoc πr ((MonoidalClosed.pre g).app T ≫ (ihom M).map b)
        ((MonoidalClosed.pre f).app T')).symm

section Modules
variable [HasCoequalizers (DayFunctor I V)] (A : CommMon (DayFunctor I V))
/-- The original balanced monoidal structure on Day modules over the selected scalar. -/
local instance originalModuleMonoidal : MonoidalCategory (Mod (DayFunctor I V) A.X) :=
  Mod.instMonoidalCategory A
/-- The original internal-Hom closed structure on Day modules over the selected scalar. -/
local instance originalModuleClosed : MonoidalClosed (Mod (DayFunctor I V) A.X) :=
  Mod.instMonoidalClosed A

/-- The original module free-unit and full Day end comparison preserve
the same entire coefficient arrow. -/
theorem fullPair_coefficient (r : I) {M' M : V} (f : M' ⟶ M)
    (N : Mod (DayFunctor I V) A.X) :
    ((FreeModuleSource.pre A (freeSequenceMap r f)).app N).hom ≫
        (NativeOmegaRecovery.FullFreeFunctionPair.comparison A r M' N).hom =
      (NativeOmegaRecovery.FullFreeFunctionPair.comparison A r M N).hom ≫
        dayTargetScalarMap r f N.X := by
  let H := (Mod.internalHom A ((Mod.free A.X).obj (freeSequence r M))).obj N
  let H' := (Mod.internalHom A ((Mod.free A.X).obj (freeSequence r M'))).obj N
  let J := (ihom (freeSequence r M)).obj N.X
  let J' := (ihom (freeSequence r M')).obj N.X
  let T := (NativeOmegaPreparation.DayIndexOrder.rightTargetFunctor r M).obj N.X
  let T' := (NativeOmegaPreparation.DayIndexOrder.rightTargetFunctor r M').obj N.X
  let p : H.X ⟶ H'.X :=
    ((FreeModuleSource.pre A (freeSequenceMap r f)).app N).hom
  let a : H.X ⟶ J := Mod.FreeInternalHom.forward A (freeSequence r M) N
  let a' : H'.X ⟶ J' := Mod.FreeInternalHom.forward A (freeSequence r M') N
  let q : J ⟶ J' := (MonoidalClosed.pre (freeSequenceMap r f)).app N.X
  let b : J ⟶ T := (dayTargetComparison r M N.X).hom
  let b' : J' ⟶ T' := (dayTargetComparison r M' N.X).hom
  let t : T ⟶ T' := dayTargetScalarMap r f N.X
  have ha : p ≫ a' = a ≫ q :=
    FreeModuleSource.pre_forward A (freeSequenceMap r f) N
  have hb : q ≫ b' = b ≫ t := dayTargetComparison_coefficient r f N.X
  change p ≫ (a' ≫ b') = (a ≫ b) ≫ t
  exact (Category.assoc p a' b').symm.trans
    ((congrArg (fun z : H.X ⟶ J' => z ≫ b') ha).trans
      ((Category.assoc a q b').trans
        ((congrArg (fun z : J ⟶ T' => a ≫ z) hb).trans
          (Category.assoc a b t).symm)))


end Modules
end PointedCGWH.Spectra.NativeStableMonoidal.DayFreeCoefficient

namespace PointedCGWH.Spectra.NativeStableMonoidal.SymmetricSmash

private abbrev I := Operad.SmallFinBijGroupoid
private abbrev V := PointedCGWH.{u, v}

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
  PointedCGWH.Spectra.NativeStableMonoidal.SymmetricSmash.monoidalCategory
  PointedCGWH.Spectra.NativeStableMonoidal.SymmetricSmash.symmetricCategory
  PointedCGWH.Spectra.NativeStableMonoidal.SymmetricSmash.monoidalClosed

/-- The original native free object with its entire pointed coefficient. -/
abbrev free (r : I) (M : V.{u, v}) :=
  Free.object (PointedCGWH.symmetricOperatorObj.{u, v} r) M

/-- Scalar tensor followed by the genuine original right-block Lan has
the original shifted cotensor as right adjoint. -/
def scalarShiftAdjunction (r : I) (M : V.{u, v}) :
    EnrichedFunctorCat.tensorLeft M ⋙
        leftKan (PointedCGWH.SymmetricShift.indexShift.{u, v} r) ⊣
      PointedCGWH.SymmetricShift.functor.{u, v} r ⋙ cotensor M :=
  (ScalarLeibniz.adjunction M).comp
    (leftKanRestrictionAdjunction (PointedCGWH.SymmetricShift.indexShift.{u, v} r))

/-- The actual balanced native smash adjunction transported only by
the proved whole original free-function comparison. -/
def freeSmashShiftAdjunction (r : I) (M : V.{u, v}) :
    NativeOmegaPreparation.NativeSymmetricFunction.smashFunctor (free r M) ⊣
      PointedCGWH.SymmetricShift.functor.{u, v} r ⋙ cotensor M :=
  (NativeOmegaPreparation.NativeSymmetricFunction.adjunction (free r M)).ofNatIsoRight
    (NativeOmegaRecovery.NativeSymmetricFreeFunction.nativeFreeComparison r M)

/-- The whole initializer retains the actual original native adjunction and free comparison. -/
theorem freeSmashShiftAdjunction_eq_original (r : I) (M : V.{u, v}) :
    freeSmashShiftAdjunction r M =
      (NativeOmegaPreparation.NativeSymmetricFunction.adjunction (free r M)).ofNatIsoRight
        (NativeOmegaRecovery.NativeSymmetricFreeFunction.nativeFreeComparison r M) := rfl

/-- The actual balanced free smash is scalar tensor followed by the genuine original coend Lan. -/
def freeSmashKanIso (r : I) (M : V.{u, v}) :
    NativeOmegaPreparation.NativeSymmetricFunction.smashFunctor (free r M) ≅
      EnrichedFunctorCat.tensorLeft M ⋙
        leftKan (PointedCGWH.SymmetricShift.indexShift.{u, v} r) :=
  Adjunction.leftAdjointUniq
    (freeSmashShiftAdjunction r M) (scalarShiftAdjunction r M)

/-- The complete original unit natural transformation commutes with
the actual scalar/coend comparison on all target objects and maps. -/
theorem freeSmashKanIso_unit (r : I) (M : V.{u, v}) :
    (freeSmashShiftAdjunction r M).unit ≫
      Functor.whiskerRight (freeSmashKanIso r M).hom
        (PointedCGWH.SymmetricShift.functor.{u, v} r ⋙ cotensor M) =
      (scalarShiftAdjunction r M).unit :=
  Adjunction.unit_leftAdjointUniq_hom
    (freeSmashShiftAdjunction r M) (scalarShiftAdjunction r M)

/-- The same complete original counit natural transformation is retained
after the actual scalar/coend comparison. -/
theorem freeSmashKanIso_counit (r : I) (M : V.{u, v}) :
    Functor.whiskerLeft (PointedCGWH.SymmetricShift.functor.{u, v} r ⋙ cotensor M)
        (freeSmashKanIso r M).hom ≫ (scalarShiftAdjunction r M).counit =
      (freeSmashShiftAdjunction r M).counit :=
  Adjunction.leftAdjointUniq_hom_counit
    (freeSmashShiftAdjunction r M) (scalarShiftAdjunction r M)

/-- Two actual native free spectra smash to the original free at s tensor r,
naturally in the entire right coefficient. -/
def freePairNatIso (r s : I) (M : V.{u, v}) :
    Free.functor (PointedCGWH.symmetricOperatorObj.{u, v} s) ⋙
        MonoidalCategory.tensorLeft (free r M) ≅
      MonoidalCategory.tensorLeft M ⋙
        Free.functor (PointedCGWH.symmetricOperatorObj.{u, v} (s ⊗ r)) :=
  Functor.isoWhiskerLeft (Free.functor (PointedCGWH.symmetricOperatorObj.{u, v} s))
      (eqToIso (PointedCGWH.Spectra.NativeStableMonoidal.SymmetricSmash.tensorLeft_eq_originalSmash
        (free r M))) ≪≫
    Functor.isoWhiskerLeft (Free.functor (PointedCGWH.symmetricOperatorObj.{u, v} s))
      (freeSmashKanIso r M) ≪≫
    (Functor.associator (Free.functor (PointedCGWH.symmetricOperatorObj.{u, v} s))
      (EnrichedFunctorCat.tensorLeft M)
      (leftKan (PointedCGWH.SymmetricShift.indexShift.{u, v} r))).symm ≪≫
    Functor.isoWhiskerRight
      (Free.scalarFreeNatIso M (PointedCGWH.symmetricOperatorObj.{u, v} s))
      (leftKan (PointedCGWH.SymmetricShift.indexShift.{u, v} r)) ≪≫
    Functor.associator (MonoidalCategory.tensorLeft M)
      (Free.functor (PointedCGWH.symmetricOperatorObj.{u, v} s))
      (leftKan (PointedCGWH.SymmetricShift.indexShift.{u, v} r)) ≪≫
    Functor.isoWhiskerLeft (MonoidalCategory.tensorLeft M)
      (HomotopicalAlgebra.EnrichedProjective.Native.Kan.leftKanFreeIso
        (PointedCGWH.SymmetricShift.indexShift.{u, v} r)
        (PointedCGWH.symmetricOperatorObj.{u, v} s))

/-- The actual free-smash comparison retains the original s tensor r source ordering. -/
def freePairIso (r s : I) (M N : V.{u, v}) :
    free r M ⊗ free s N ≅ free (s ⊗ r) (M ⊗ N) :=
  (freePairNatIso r s M).app N

/-- Every complete original right coefficient map commutes with the actual
two-free smash comparison. -/
theorem freePairIso_right (r s : I) (M : V.{u, v}) {N N' : V.{u, v}} (f : N ⟶ N') :
    let Fs : V.{u, v} ⥤
        EnrichedFunctorCat V.{u, v} PointedCGWH.SymmetricOperatorIndex.{u, v} :=
      Free.functor (PointedCGWH.symmetricOperatorObj.{u, v} s)
    let Ts : EnrichedFunctorCat V.{u, v} PointedCGWH.SymmetricOperatorIndex.{u, v} ⥤
        EnrichedFunctorCat V.{u, v} PointedCGWH.SymmetricOperatorIndex.{u, v} :=
      MonoidalCategory.tensorLeft (free r M)
    let G : V.{u, v} ⥤
        EnrichedFunctorCat V.{u, v} PointedCGWH.SymmetricOperatorIndex.{u, v} :=
      MonoidalCategory.tensorLeft M ⋙
        Free.functor (PointedCGWH.symmetricOperatorObj.{u, v} (s ⊗ r))
    let e : Fs ⋙ Ts ≅ G := freePairNatIso r s M
    (Fs ⋙ Ts).map (X := N) (Y := N') f ≫ e.hom.app N' =
      e.hom.app N ≫ G.map (X := N) (Y := N') f := by
  intro Fs Ts G e
  exact e.hom.naturality f


end PointedCGWH.Spectra.NativeStableMonoidal.SymmetricSmash

namespace PointedCGWH.Spectra.NativeStableMonoidal.FreePairTransport

universe uC vC uD vD uT vT

/-- The actual tensor transported through an equivalence acts on the whole
pair of coefficient functors by its original inverse and forward maps. -/
theorem transportedPair_eq
    {C : Type uC} [Category.{vC} C] [MonoidalCategory C]
    {D : Type uD} [Category.{vD} D] (E : C ≌ D)
    {T : Type uT} [Category.{vT} T] (F G : T ⥤ D) :
    letI : MonoidalCategory D := Monoidal.transport E
    F.prod G ⋙ tensor D =
      ((F ⋙ E.inverse).prod (G ⋙ E.inverse) ⋙ tensor C) ⋙ E.functor := rfl

universe uO vO

/-- The same complete whiskered isomorphism has the original composed pair as its source. -/
private def wholeBalancedPairWhisker
    {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
    {B : Type uT} [Category.{vT} B] {O : Type uO} [Category.{vO} O]
    (F : C ⥤ D) (T : D × D ⥤ D) (S : C × C ⥤ C) (E : D ⥤ O)
    (P Q : B ⥤ C) (e : F.prod F ⋙ T ≅ S ⋙ F) :
    ((P ⋙ F).prod (Q ⋙ F) ⋙ T) ⋙ E ≅ (P.prod Q ⋙ (S ⋙ F)) ⋙ E :=
  Functor.isoWhiskerRight (Functor.isoWhiskerLeft (P.prod Q) e) E

end PointedCGWH.Spectra.NativeStableMonoidal.FreePairTransport

namespace PointedCGWH.Spectra.NativeStableMonoidal.SymmetricSmash

private abbrev PairSequence := PointedCGWH.SymmetricSequence.{u, v}
private abbrev PairSphere := PointedCGWH.sphereSequence.{u, v}
private abbrev PairSphereMon := PointedCGWH.sphereSequenceCommMon.{u, v}
private abbrev PairCarrier :=
  EnrichedFunctorCat V.{u, v} PointedCGWH.SymmetricOperatorIndex.{u, v}
private abbrev PairEquivalence :=
  PointedCGWH.SymmetricModulePresentation.moduleOperatorEquivalence.{u, v}

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
  PointedCGWH.Spectra.NativeStableMonoidal.SymmetricSmash.monoidalCategory
  PointedCGWH.Spectra.NativeStableMonoidal.SymmetricSmash.symmetricCategory
  PointedCGWH.Spectra.NativeStableMonoidal.SymmetricSmash.monoidalClosed

private abbrev PairModules := CategoryTheory.Mod PairSequence.{u, v} PairSphere.{u, v}

/-- The original balanced monoidal structure on the selected sphere-module carrier. -/
local instance pairModulesMonoidal : MonoidalCategory PairModules.{u, v} :=
  Mod.instMonoidalCategory PairSphereMon.{u, v}

private def pairNativeFree (r : I) : V.{u, v} ⥤ PairCarrier.{u, v} :=
  Free.functor (V := V.{u, v}) (PointedCGWH.symmetricOperatorObj.{u, v} r)

private def pairRepresented (r : I) : V.{u, v} ⥤ PairSequence.{u, v} :=
  Operad.SmallFinBijGroupoid.RepresentablePair.represented (V := V.{u, v}) r

private def pairSource (r s : I) : V.{u, v} × V.{u, v} ⥤ PairCarrier.{u, v} :=
  (pairNativeFree r).prod (pairNativeFree s) ⋙ tensor PairCarrier.{u, v}

private def pairTarget (r s : I) : V.{u, v} × V.{u, v} ⥤ PairCarrier.{u, v} :=
  tensor V.{u, v} ⋙ pairNativeFree (s ⊗ r)

private def pairTensorModules (F G : V.{u, v} ⥤ PairModules.{u, v}) :
    V.{u, v} × V.{u, v} ⥤ PairCarrier.{u, v} :=
  (F.prod G ⋙ tensor PairModules.{u, v}) ⋙ PairEquivalence.{u, v}.functor

private def pairFreeToModules (r : I) : V.{u, v} ⥤ PairModules.{u, v} :=
  pairNativeFree r ⋙ PairEquivalence.{u, v}.inverse

private def pairDayFree (r : I) : V.{u, v} ⥤ PairModules.{u, v} :=
  Mod.dayFreeAt PairSphere.{u, v} r

private def pairAmbient (r s : I) :
    V.{u, v} × V.{u, v} ⥤ PairSequence.{u, v} × PairSequence.{u, v} :=
  (pairRepresented r).prod (pairRepresented s)

private def pairSequenceFree : PairSequence.{u, v} ⥤ PairModules.{u, v} :=
  Mod.free PairSphere.{u, v}

private def pairTensorResult (r s : I) : V.{u, v} × V.{u, v} ⥤ PairCarrier.{u, v} :=
  (pairAmbient r s ⋙ (tensor PairSequence.{u, v} ⋙ pairSequenceFree.{u, v})) ⋙
    PairEquivalence.{u, v}.functor

private def pairDayResult (r s : I) : V.{u, v} × V.{u, v} ⥤ PairCarrier.{u, v} :=
  tensor V.{u, v} ⋙ (pairDayFree (s ⊗ r) ⋙ PairEquivalence.{u, v}.functor)

private def pairTransportIso (r s : I) :
    pairSource r s ≅ pairTensorModules (pairFreeToModules r) (pairFreeToModules s) := by
  unfold pairSource pairTensorModules pairFreeToModules
  exact eqToIso (FreePairTransport.transportedPair_eq PairEquivalence.{u, v}
    (pairNativeFree r) (pairNativeFree s))

private def pairSourceComparisonIso (r s : I) :
    pairTensorModules (pairFreeToModules r) (pairFreeToModules s) ≅
      pairTensorModules (pairDayFree r) (pairDayFree s) := by
  unfold pairTensorModules pairFreeToModules pairDayFree pairNativeFree
  exact Functor.isoWhiskerRight
    (Functor.isoWhiskerRight
      (NatIso.prod (NativeOmegaPreparation.SymmetricNativeFree.comparison.{u, v} r).symm
        (NativeOmegaPreparation.SymmetricNativeFree.comparison.{u, v} s).symm)
      (tensor PairModules.{u, v})) PairEquivalence.{u, v}.functor

private def pairBalancedIso (r s : I) :
    pairTensorModules (pairDayFree r) (pairDayFree s) ≅ pairTensorResult r s := by
  let F : PairSequence.{u, v} ⥤ PairModules.{u, v} := Mod.free PairSphere.{u, v}
  let T : PairModules.{u, v} × PairModules.{u, v} ⥤ PairModules.{u, v} :=
    tensor PairModules.{u, v}
  let S : PairSequence.{u, v} × PairSequence.{u, v} ⥤ PairSequence.{u, v} :=
    tensor PairSequence.{u, v}
  let E : PairModules.{u, v} ⥤ PairCarrier.{u, v} := PairEquivalence.{u, v}.functor
  let e : F.prod F ⋙ T ≅ S ⋙ F :=
    @Mod.FreePairRelativeTensor.bifunctorIso PairSequence.{u, v} inferInstance
      PointedCGWH.originalSymmetricSequenceMonoidal.{u, v}
      PointedCGWH.originalSymmetricSequenceBraided.{u, v}
      PairSphereMon.{u, v}
      NativeOmegaPreparation.SymmetricFunction.sequenceCoequalizers.{u, v}
      (fun X => inferInstance) (fun X => inferInstance)
  exact FreePairTransport.wholeBalancedPairWhisker F T S E
    (pairRepresented r) (pairRepresented s) e

private def pairDayIso (r s : I) : pairTensorResult r s ≅ pairDayResult r s := by
  unfold pairTensorResult pairDayResult pairAmbient pairRepresented pairDayFree pairSequenceFree
  exact Functor.isoWhiskerRight
    (Functor.isoWhiskerRight
      (Operad.SmallFinBijGroupoid.RepresentablePair.orderedBifunctorIso (V := V.{u, v}) r s)
      (Mod.free PairSphere.{u, v})) PairEquivalence.{u, v}.functor

private def pairOperatorIso (r s : I) : pairDayResult r s ≅ pairTarget r s := by
  unfold pairDayResult pairTarget pairDayFree pairNativeFree
  exact Functor.isoWhiskerLeft (tensor V.{u, v})
    (NativeOmegaPreparation.SymmetricNativeFree.operatorComparison.{u, v} (s ⊗ r))

universe u_1 u_2

/-- The full two-coefficient native free-smash comparison, from the actual
module presentation, balancing coequalizer, both Day collapses and index braid. -/
def freePairBifunctorIso (r s : I) :
    pairSource.{u_2, u_1} r s ≅ pairTarget.{u_2, u_1} r s :=
  pairTransportIso r s ≪≫ pairSourceComparisonIso r s ≪≫ pairBalancedIso r s ≪≫
    pairDayIso r s ≪≫ pairOperatorIso r s

/-- The complete original two-free functor comparison retains all five original
module, Day, and operator factors in its declared native frame. -/
theorem freePairBifunctorIso_original_factors (r s : I) :
    freePairBifunctorIso.{u, v} r s =
      pairTransportIso r s ≪≫ pairSourceComparisonIso r s ≪≫ pairBalancedIso r s ≪≫
        pairDayIso r s ≪≫ pairOperatorIso r s := by
  rfl

/-- The actual native free pair, with all original scalar coefficient data. -/
def freePairBothIso (r s : I) (M N : V.{u, v}) :
    free r M ⊗ free s N ≅ free (s ⊗ r) (M ⊗ N) :=
  (freePairBifunctorIso r s).app (M, N)

/-- The complete original source transport retains the same original equality isomorphism. -/
theorem freePairSourceTransport_original (r s : I) :
    pairTransportIso.{u, v} r s =
      eqToIso (FreePairTransport.transportedPair_eq PairEquivalence.{u, v}
        (pairNativeFree.{u, v} r) (pairNativeFree.{u, v} s)) := by
  rfl

/-- Both complete original source comparisons retain their actual tensor and carrier whiskerings. -/
theorem freePairSourceComparison_original (r s : I) :
    pairSourceComparisonIso.{u, v} r s =
      Functor.isoWhiskerRight
        (Functor.isoWhiskerRight
          (NatIso.prod (NativeOmegaPreparation.SymmetricNativeFree.comparison.{u, v} r).symm
            (NativeOmegaPreparation.SymmetricNativeFree.comparison.{u, v} s).symm)
          (tensor PairModules.{u, v})) PairEquivalence.{u, v}.functor := by
  rfl

/-- The entire original balanced factor retains its true two-free module comparison and original whiskering. -/
theorem freePairBalanced_original (r s : I) :
    pairBalancedIso.{u, v} r s =
      (let F : PairSequence.{u, v} ⥤ PairModules.{u, v} := Mod.free PairSphere.{u, v}
       let T : PairModules.{u, v} × PairModules.{u, v} ⥤ PairModules.{u, v} := tensor PairModules.{u, v}
       let S : PairSequence.{u, v} × PairSequence.{u, v} ⥤ PairSequence.{u, v} := tensor PairSequence.{u, v}
       let E : PairModules.{u, v} ⥤ PairCarrier.{u, v} := PairEquivalence.{u, v}.functor
       let e : F.prod F ⋙ T ≅ S ⋙ F :=
         @Mod.FreePairRelativeTensor.bifunctorIso PairSequence.{u, v} inferInstance
           PointedCGWH.originalSymmetricSequenceMonoidal.{u, v}
           PointedCGWH.originalSymmetricSequenceBraided.{u, v}
           PairSphereMon.{u, v}
           NativeOmegaPreparation.SymmetricFunction.sequenceCoequalizers.{u, v}
           (fun _X => inferInstance) (fun _X => inferInstance)
       FreePairTransport.wholeBalancedPairWhisker F T S E
         (pairRepresented r) (pairRepresented s) e) := by
  rfl

/-- The original Day inverse keeps the full original ordered pair and free module map. -/
theorem freePairDay_inv_component (r s : I) (M N : V.{u, v}) :
    (pairDayIso.{u, v} r s).inv.app (M, N) =
      PairEquivalence.{u, v}.functor.map ((Mod.free PairSphere.{u, v}).map
        (Operad.SmallFinBijGroupoid.RepresentablePair.orderedIso (V := V.{u, v}) r s M N).inv) := by
  rfl

/-- The original operator inverse retains the actual free comparison at its complete coefficient tensor. -/
theorem freePairOperator_inv_component (r s : I) (M N : V.{u, v}) :
    (pairOperatorIso.{u, v} r s).inv.app (M, N) =
      (NativeOmegaPreparation.SymmetricNativeFree.operatorComparison.{u, v} (s ⊗ r)).inv.app (M ⊗ N) := by
  rfl

/-- Both native coefficient maps commute with the actual balanced pair comparison. -/
theorem freePairBothIso_coefficient (r s : I)
    {M M' N N' : V.{u, v}} (f : M ⟶ M') (g : N ⟶ N') :
    (pairSource r s).map (f, g) ≫ (freePairBifunctorIso r s).hom.app (M', N') =
      (freePairBifunctorIso r s).hom.app (M, N) ≫ (pairTarget r s).map (f, g) :=
  let p : (M, N) ⟶ (M', N') := (f, g)
  let e : pairSource.{u, v} r s ≅ pairTarget.{u, v} r s := freePairBifunctorIso r s
  e.hom.naturality p

universe uB vB uD vD

private theorem pairTensorFunctor_map
    {B : Type uB} [Category.{vB} B] {D : Type uD} [Category.{vD} D] [MonoidalCategory D]
    (F G : B ⥤ D) {M M' N N' : B} (f : M ⟶ M') (g : N ⟶ N') :
    (F.prod G ⋙ tensor D).map (X := (M, N)) (Y := (M', N')) (f, g) = F.map f ⊗ₘ G.map g := rfl

private theorem tensorCoefficientFunctor_map
    {B : Type uB} [Category.{vB} B] [MonoidalCategory B] {D : Type uD} [Category.{vD} D]
    (F : B ⥤ D) {M M' N N' : B} (f : M ⟶ M') (g : N ⟶ N') :
    (tensor B ⋙ F).map (X := (M, N)) (Y := (M', N')) (f, g) = F.map (f ⊗ₘ g) := rfl

set_option maxHeartbeats 500000 in
-- Read the literal original coefficient maps at this typed constructor boundary.
private theorem pairSource_map_literal (r s : I)
    {M M' N N' : V.{u, v}} (f : M ⟶ M') (g : N ⟶ N') :
    (pairSource r s).map (X := (M, N)) (Y := (M', N')) (f, g) =
      ((Free.functor (V := V.{u, v}) (PointedCGWH.symmetricOperatorObj r)).map f) ⊗ₘ
        ((Free.functor (V := V.{u, v}) (PointedCGWH.symmetricOperatorObj s)).map g) := by
  simpa only [pairSource, pairNativeFree] using pairTensorFunctor_map
    (Free.functor (V := V.{u, v}) (PointedCGWH.symmetricOperatorObj r))
    (Free.functor (V := V.{u, v}) (PointedCGWH.symmetricOperatorObj s)) f g

set_option maxHeartbeats 500000 in
-- Read the literal original coefficient maps at this typed constructor boundary.
private theorem pairTarget_map_literal (r s : I)
    {M M' N N' : V.{u, v}} (f : M ⟶ M') (g : N ⟶ N') :
    (pairTarget r s).map (X := (M, N)) (Y := (M', N')) (f, g) =
      (Free.functor (V := V.{u, v}) (PointedCGWH.symmetricOperatorObj (s ⊗ r))).map (f ⊗ₘ g) := by
  simpa only [pairTarget, pairNativeFree] using tensorCoefficientFunctor_map
    (Free.functor (V := V.{u, v}) (PointedCGWH.symmetricOperatorObj (s ⊗ r))) f g

private theorem pairComparison_hom_literal (r s : I) (M N : V.{u, v}) :
    (freePairBifunctorIso r s).hom.app (M, N) = (freePairBothIso r s M N).hom := rfl

universe uC vC

private theorem pointwiseSquareOfMaps
    {C : Type uC} [Category.{vC} C] {X Y Z W : C}
    {p p' : X ⟶ Y} {s s' : Y ⟶ W} {e e' : X ⟶ Z} {q q' : Z ⟶ W}
    (h : p ≫ s = e ≫ q) (hp : p = p') (hs : s = s') (he : e = e') (hq : q = q') :
    p' ≫ s' = e' ≫ q' := by
  rw [← hp, ← hs, ← he, ← hq]
  exact h

/-- The direct pointwise coefficient contract retains the literal original
free-functor maps and the actual original two-free comparison. -/
def FreePairBothCoefficient (r s : I)
    {M M' N N' : V.{u, v}} (f : M ⟶ M') (g : N ⟶ N') : Prop :=
  (((Free.functor (V := V.{u, v}) (PointedCGWH.symmetricOperatorObj r)).map f) ⊗ₘ
      ((Free.functor (V := V.{u, v}) (PointedCGWH.symmetricOperatorObj s)).map g)) ≫
      (freePairBothIso r s M' N').hom =
    (freePairBothIso r s M N).hom ≫
      (Free.functor (V := V.{u, v}) (PointedCGWH.symmetricOperatorObj (s ⊗ r))).map (f ⊗ₘ g)

set_option maxHeartbeats 500000 in
-- Expose the original literal native coefficient endpoints once in a typed public contract.
/-- Both literal original coefficient arrows preserve the actual two-free
comparison for every original index and pointed coefficient. -/
theorem freePairBothIso_coefficient_pointwise (r s : I)
    {M M' N N' : V.{u, v}} (f : M ⟶ M') (g : N ⟶ N') :
    FreePairBothCoefficient r s f g := by
  have h := pointwiseSquareOfMaps (C := PairCarrier.{u, v})
    (freePairBothIso_coefficient r s f g)
    (pairSource_map_literal r s f g) (pairComparison_hom_literal r s M' N')
    (pairComparison_hom_literal r s M N) (pairTarget_map_literal r s f g)
  exact h

/-!
## The complete source frame of the original two-free comparison

The source frame retains the actual module and carrier dictionaries used
above. Its whole comparison is identified with `freePairBifunctorIso`
before any source, coefficient or unit component is selected.
-/

namespace SourceFactors

/-- The original symmetric-sequence category of the balanced source. -/
abbrev Sequence := PairSequence.{u, v}

/-- The original right sphere-module source category. -/
abbrev Modules := PairModules.{u, v}

/-- The original native enriched operator carrier. -/
abbrev Carrier := PairCarrier.{u, v}

/-- The actual source-module tensor dictionary used by the original pair. -/
@[instance_reducible]
def moduleMonoidal : MonoidalCategory Modules.{u, v} := pairModulesMonoidal.{u, v}

attribute [local instance] moduleMonoidal

/-- The complete original module/operator equivalence, on objects and arrows. -/
def equivalence : Modules.{u, v} ≌ Carrier.{u, v} := PairEquivalence.{u, v}

/-- The unchanged native enriched free functor at each original source index. -/
def nativeFree (r : I) : V.{u, v} ⥤ Carrier.{u, v} := pairNativeFree.{u, v} r

/-- The actual represented Day coefficient functor at each source index. -/
def represented (r : I) : V.{u, v} ⥤ Sequence.{u, v} := pairRepresented.{u, v} r

/-- Both whole native free functors and their original source equivalence. -/
def originalTransportData (r s : I) :
    Monoidal.TransportPairSource.TransportPairData
      (C := Modules.{u, v}) (D := Carrier.{u, v}) (K := V.{u, v}) where
  equivalence := equivalence.{u, v}
  leftFree := nativeFree.{u, v} r
  rightFree := nativeFree.{u, v} s

/-- The complete original two-native-free tensor functor. -/
def nativeTensor (r s : I) : V.{u, v} × V.{u, v} ⥤ Carrier.{u, v} := pairSource.{u, v} r s

/-- The complete original coefficient-tensor free target at the ordered index. -/
def target (r s : I) : V.{u, v} × V.{u, v} ⥤ Carrier.{u, v} := pairTarget.{u, v} r s

/-- The original inverse-carrier pair tensor followed by its forward carrier. -/
def inverseTensor (r s : I) : V.{u, v} × V.{u, v} ⥤ Carrier.{u, v} :=
  pairTensorModules.{u, v} (pairFreeToModules.{u, v} r) (pairFreeToModules.{u, v} s)

/-- The original balanced tensor of the two actual free sphere-module functors. -/
def freeTensor (r s : I) : V.{u, v} × V.{u, v} ⥤ Carrier.{u, v} :=
  pairTensorModules.{u, v} (pairDayFree.{u, v} r) (pairDayFree.{u, v} s)

/-- The original ordered Day tensor target before the operator comparison. -/
def orderedTensor (r s : I) : V.{u, v} × V.{u, v} ⥤ Carrier.{u, v} := pairDayResult.{u, v} r s

/-- The actual native tensor/source cast from the same original equivalence. -/
def transport (r s : I) : nativeTensor.{u, v} r s ≅ inverseTensor.{u, v} r s :=
  pairTransportIso.{u, v} r s

/-- Both entire original free comparisons precede the module tensor and carrier. -/
def sourceComparison (r s : I) : inverseTensor.{u, v} r s ≅ freeTensor.{u, v} r s :=
  pairSourceComparisonIso.{u, v} r s

/-- The complete free-module balancing data retain all original coefficient functors. -/
def originalBalancedData (r s : I) :
    Monoidal.TransportPairSource.BalancedPairData
      (S := Sequence.{u, v}) (M := Modules.{u, v}) (B := V.{u, v}) (O := Carrier.{u, v}) where
  free := pairSequenceFree.{u, v}
  moduleTensor := tensor Modules.{u, v}
  sequenceTensor := tensor Sequence.{u, v}
  carrier := equivalence.{u, v}.functor
  left := represented.{u, v} r
  right := represented.{u, v} s
  comparison :=
    @Mod.FreePairRelativeTensor.bifunctorIso PairSequence.{u, v} inferInstance
      PointedCGWH.originalSymmetricSequenceMonoidal.{u, v}
      PointedCGWH.originalSymmetricSequenceBraided.{u, v}
      PairSphereMon.{u, v}
      NativeOmegaPreparation.SymmetricFunction.sequenceCoequalizers.{u, v}
      (fun X => inferInstance) (fun X => inferInstance)

/-- The actual full balanced comparison from the original free-module adjunction. -/
def balanced (r s : I) : freeTensor.{u, v} r s ≅ pairTensorResult.{u, v} r s :=
  pairBalancedIso.{u, v} r s

/-- The original ordered Day pair and complete block permutation. -/
def ordered (r s : I) : pairTensorResult.{u, v} r s ≅ orderedTensor.{u, v} r s :=
  pairDayIso.{u, v} r s

/-- The original complete free/evaluation operator comparison. -/
def operator (r s : I) : orderedTensor.{u, v} r s ≅ target.{u, v} r s := pairOperatorIso.{u, v} r s

/-- The whole actual native pair comparison, in its original full source frame. -/
def comparison (r s : I) : nativeTensor.{u, v} r s ≅ target.{u, v} r s :=
  freePairBifunctorIso.{v, u} r s

/-- The complete source frame keeps the exact original native pair isomorphism. -/
theorem comparison_original (r s : I) :
    comparison.{u, v} r s = freePairBifunctorIso.{v, u} r s := rfl

/-- Every coefficient pair retains both maps of the exact original native free comparison. -/
theorem comparison_app (r s : I) (M N : V.{u, v}) :
    (comparison.{u, v} r s).app (M, N) = freePairBothIso.{u, v} r s M N := rfl

/-- The whole original comparison retains all five source, free, balancing, Day and operator maps. -/
theorem comparison_eq_factors (r s : I) :
    comparison.{u, v} r s = transport.{u, v} r s ≪≫ sourceComparison.{u, v} r s ≪≫
      balanced.{u, v} r s ≪≫ ordered.{u, v} r s ≪≫ operator.{u, v} r s := rfl

/-- The actual source cast retains the whole original equivalence and both free functors. -/
theorem transport_eq_original_data (r s : I) :
    transport.{u, v} r s =
      Monoidal.TransportPairSource.TransportPairData.castIso (originalTransportData.{u, v} r s) := rfl

/-- The original balancing factor is the complete whiskering of its actual source data. -/
theorem balanced_eq_original_data (r s : I) :
    balanced.{u, v} r s =
      Monoidal.TransportPairSource.BalancedPairData.iso (originalBalancedData.{u, v} r s) := rfl

end SourceFactors

end PointedCGWH.Spectra.NativeStableMonoidal.SymmetricSmash
