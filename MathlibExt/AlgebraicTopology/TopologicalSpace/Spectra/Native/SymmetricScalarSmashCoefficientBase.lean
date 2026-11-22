/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.SymmetricScalarSmash
import MathlibExt.AlgebraicTopology.Spectra.Symmetric.PointedCGWH.FunctionSpectrum.FreeSourceCoefficientData
import MathlibExt.AlgebraicTopology.Spectra.Symmetric.PointedCGWH.FunctionSpectrum.SourceCoefficientSourceFactors
import MathlibExt.CategoryTheory.Enriched.ScalarCorners

/-!
# The entire original module/operator coefficient square

The full original module coefficient square is carried through the actual
operator equivalence and its original counit. The source equality and actual
right functor unitor preserve every original factor map, free degree,
coefficient arrow and target.
-/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open CategoryTheory.EnrichedFunctorCat
open scoped MonoidalCategory MonoidalClosed CategoryTheory.MonObj

namespace PointedCGWH.Spectra.NativeStableMonoidal.SymmetricScalarSmash.Primitive

universe uC vC uD vD
variable {C : Type uC} [Category.{vC} C] [MonoidalCategory C] [BraidedCategory C]
  [MonoidalClosed C] [HasEqualizers C] [HasCoequalizers C]
  {D : Type uD} [Category.{vD} D] (A : CommMon C) (E : Mod C A.X ≌ D)

/-- The tensor on modules over `A` used by the primitive scalar-smash source comparison. -/
local instance moduleMonoidal : MonoidalCategory (Mod C A.X) := Mod.instMonoidalCategory A
/-- The module internal Hom structure used by the primitive contravariant source comparison. -/
local instance moduleClosed : MonoidalClosed (Mod C A.X) := Mod.instMonoidalClosed A

/-- The original module-function source equality is natural in the entire original module arrow. -/
theorem sourceComparison_naturality {M M' : Mod C A.X} (f : M' ⟶ M) :
    (NativeOmegaPreparation.ModuleFunctionTransport.sourceFunctor A E).map f.op ≫
      (eqToIso (NativeOmegaPreparation.ModuleFunctionTransport.sourceFunctor_obj A E M')).hom =
    (eqToIso (NativeOmegaPreparation.ModuleFunctionTransport.sourceFunctor_obj A E M)).hom ≫
      Functor.whiskerLeft E.inverse (Functor.whiskerRight (MonoidalClosed.pre f) E.functor) := by
  apply NatTrans.ext
  funext X
  change E.functor.map ((MonoidalClosed.pre f).app (E.inverse.obj X)) ≫ 𝟙 _ =
    𝟙 _ ≫ E.functor.map ((MonoidalClosed.pre f).app (E.inverse.obj X))
  simp only [Category.comp_id, Category.id_comp]

/-- The same original source square keeps the literal full free-coefficient pre-map. -/
theorem sourceComparison_free_naturality {P P' : C} (p : P' ⟶ P) :
    (NativeOmegaPreparation.ModuleFunctionTransport.sourceFunctor A E).map
        ((Mod.free A.X).map p).op ≫
      (eqToIso (NativeOmegaPreparation.ModuleFunctionTransport.sourceFunctor_obj A E
        ((Mod.free A.X).obj P'))).hom =
    (eqToIso (NativeOmegaPreparation.ModuleFunctionTransport.sourceFunctor_obj A E
      ((Mod.free A.X).obj P))).hom ≫
      Functor.whiskerLeft E.inverse (Functor.whiskerRight (FreeModuleSource.pre A p) E.functor) :=
  sourceComparison_naturality A E ((Mod.free A.X).map p)

end PointedCGWH.Spectra.NativeStableMonoidal.SymmetricScalarSmash.Primitive

namespace PointedCGWH.Spectra.NativeStableMonoidal.SymmetricScalarSmash.Primitive

universe uC vC uD vD uE vE
variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
  {E : Type uE} [Category.{vE} E]

/-- Whiskering retains a whole given square of the actual original natural transformations. -/
theorem whiskerLeftSquare (K : C ⥤ D) {F F' G G' : D ⥤ E}
    {p : F ⟶ F'} {c : F ⟶ G} {c' : F' ⟶ G'} {q : G ⟶ G'}
    (h : p ≫ c' = c ≫ q) :
    Functor.whiskerLeft K p ≫ Functor.whiskerLeft K c' =
      Functor.whiskerLeft K c ≫ Functor.whiskerLeft K q := by
  apply NatTrans.ext
  funext X
  exact congrArg (fun t ↦ t.app (K.obj X)) h

/-- The actual carrier functor pins both category instances before the whole source squares are pasted. -/
theorem pasteThroughCarrier (L : C ⥤ D)
    {F F' G G' : C ⥤ C} {R R' : D ⥤ D}
    {p : F ⟶ F'} {g : G ⟶ G'} {q : R ⟶ R'}
    (m : F ≅ G) (m' : F' ≅ G')
    (r : G ⋙ L ≅ L ⋙ R) (r' : G' ⋙ L ≅ L ⋙ R')
    (c : F ⋙ L ≅ L ⋙ R) (c' : F' ⋙ L ≅ L ⋙ R')
    (hc : c.hom = (Functor.isoWhiskerRight m L).hom ≫ r.hom)
    (hc' : c'.hom = (Functor.isoWhiskerRight m' L).hom ≫ r'.hom)
    (hm : Functor.whiskerRight p L ≫ (Functor.isoWhiskerRight m' L).hom =
      (Functor.isoWhiskerRight m L).hom ≫ Functor.whiskerRight g L)
    (hr : Functor.whiskerRight g L ≫ r'.hom = r.hom ≫ Functor.whiskerLeft L q) :
    Functor.whiskerRight p L ≫ c'.hom = c.hom ≫ Functor.whiskerLeft L q := by
  rw [hc, hc']
  calc
    _ = (Functor.whiskerRight p L ≫ (Functor.isoWhiskerRight m' L).hom) ≫ r'.hom :=
      (Category.assoc _ _ _).symm
    _ = ((Functor.isoWhiskerRight m L).hom ≫ Functor.whiskerRight g L) ≫ r'.hom :=
      congrArg (fun f => f ≫ r'.hom) hm
    _ = (Functor.isoWhiskerRight m L).hom ≫
        (Functor.whiskerRight g L ≫ r'.hom) := Category.assoc _ _ _
    _ = (Functor.isoWhiskerRight m L).hom ≫ (r.hom ≫ Functor.whiskerLeft L q) :=
      congrArg (fun f => (Functor.isoWhiskerRight m L).hom ≫ f) hr
    _ = _ := (Category.assoc _ _ _).symm

end PointedCGWH.Spectra.NativeStableMonoidal.SymmetricScalarSmash.Primitive

namespace PointedCGWH.Spectra.NativeStableMonoidal.SymmetricScalarSmash.Primitive

universe uC vC uD vD
variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]

/-- The given entire original comparisons retain the coefficient square after an actual counit collapse. -/
theorem identifiedCollapseCoefficient (E : C ≌ D)
    {F F' : C ⥤ C} {R R' : D ⥤ D}
    (p : F ⟶ F') (q : R ⟶ R')
    (e : F ≅ E.functor ⋙ R ⋙ E.inverse) (e' : F' ≅ E.functor ⋙ R' ⋙ E.inverse)
    (g : E.functor ⋙ R ⋙ E.inverse ⟶ E.functor ⋙ R' ⋙ E.inverse)
    (c : F ⋙ E.functor ≅ E.functor ⋙ R) (c' : F' ⋙ E.functor ≅ E.functor ⋙ R')
    (hc : c = NativeOmegaRecovery.FreeFunctionCarrierComparison.collapse E e)
    (hc' : c' = NativeOmegaRecovery.FreeFunctionCarrierComparison.collapse E e')
    (hg : g = Functor.whiskerLeft E.functor (Functor.whiskerRight q E.inverse))
    (h : p ≫ e'.hom = e.hom ≫ g) :
    Functor.whiskerRight p E.functor ≫ c'.hom = c.hom ≫ Functor.whiskerLeft E.functor q := by
  rw [hc, hc']
  exact NativeOmegaRecovery.FreeFunctionCarrierComparison.collapse_coefficient_with_target E p q e e' g hg h

/-- The given original square fixes its full source map before the original counit is collapsed. -/
theorem collapseOriginalSquare (E : C ≌ D)
    {F F' : C ⥤ C} {R R' : D ⥤ D}
    (q : R ⟶ R')
    (e : F ≅ E.functor ⋙ R ⋙ E.inverse) (e' : F' ≅ E.functor ⋙ R' ⋙ E.inverse)
    {p : F ⟶ F'}
    {g : E.functor ⋙ R ⋙ E.inverse ⟶ E.functor ⋙ R' ⋙ E.inverse}
    (h : p ≫ e'.hom = e.hom ≫ g)
    (hg : g = Functor.whiskerLeft E.functor (Functor.whiskerRight q E.inverse))
    (c : F ⋙ E.functor ≅ E.functor ⋙ R) (c' : F' ⋙ E.functor ≅ E.functor ⋙ R')
    (hc : c = NativeOmegaRecovery.FreeFunctionCarrierComparison.collapse E e)
    (hc' : c' = NativeOmegaRecovery.FreeFunctionCarrierComparison.collapse E e') :
    Functor.whiskerRight p E.functor ≫ c'.hom = c.hom ≫ Functor.whiskerLeft E.functor q :=
  identifiedCollapseCoefficient E p q e e' g c c' hc hc' hg h

end PointedCGWH.Spectra.NativeStableMonoidal.SymmetricScalarSmash.Primitive

namespace PointedCGWH.Spectra.NativeStableMonoidal.SymmetricScalarSmash.Primitive

universe uW vW
variable {W : Type uW} [Category.{vW} W]

/-- Whole source squares paste with independent object and Hom universes. -/
theorem pasteSquares {H H' G G' K K' : W}
    {p : H ⟶ H'} {e : H ⟶ G} {e' : H' ⟶ G'} {b : G ⟶ G'}
    {t : G ⟶ K} {t' : G' ⟶ K'} {k : K ⟶ K'} {c : H ⟶ K} {c' : H' ⟶ K'}
    (hc : c = e ≫ t) (hc' : c' = e' ≫ t')
    (hs : p ≫ e' = e ≫ b) (ht : b ≫ t' = t ≫ k) : p ≫ c' = c ≫ k := by
  rw [hc, hc']
  calc
    _ = (p ≫ e') ≫ t' := (Category.assoc p e' t').symm
    _ = (e ≫ b) ≫ t' := congrArg (fun f => f ≫ t') hs
    _ = e ≫ (b ≫ t') := Category.assoc e b t'
    _ = e ≫ (t ≫ k) := congrArg (fun f => e ≫ f) ht
    _ = _ := (Category.assoc e t k).symm

/-- Three original source squares preserve the complete comparison specified by their actual factorization. -/
theorem coefficientOfFactors
    {H H' G G' L L' K K' : W}
    (s : H ≅ G) (s' : H' ≅ G') (m : G ≅ L) (m' : G' ≅ L')
    (r : L ≅ K) (r' : L' ≅ K') (c : H ≅ K) (c' : H' ≅ K')
    {p : H ⟶ H'} {q : G ⟶ G'} {t : L ⟶ L'} {k : K ⟶ K'}
    (hc : c = s ≪≫ m ≪≫ r) (hc' : c' = s' ≪≫ m' ≪≫ r')
    (hs : p ≫ s'.hom = s.hom ≫ q)
    (hm : q ≫ m'.hom = m.hom ≫ t)
    (hr : t ≫ r'.hom = r.hom ≫ k) : p ≫ c'.hom = c.hom ≫ k := by
  rw [hc, hc']
  simp only [Iso.trans_hom]
  exact pasteSquares rfl rfl hs (pasteSquares rfl rfl hm hr)

/-- Both original free-source isomorphisms transfer the complete source comparison square. -/
theorem inverseSourceCoefficient {S S' H H' K K' : W}
    (e : S ≅ H) (e' : S' ≅ H') (c : S ≅ K) (c' : S' ≅ K')
    {p : H ⟶ H'} {q : S ⟶ S'} {k : K ⟶ K'}
    (hFree : e.hom ≫ p = q ≫ e'.hom) (hComparison : q ≫ c'.hom = c.hom ≫ k) :
    p ≫ (e'.symm ≪≫ c').hom = (e.symm ≪≫ c).hom ≫ k := by
  have h : p ≫ e'.inv = e.inv ≫ q := by
    apply (cancel_mono e'.hom).mp
    rw [Category.assoc, e'.inv_hom_id, Category.comp_id, Category.assoc, ← hFree,
      ← Category.assoc, e.inv_hom_id, Category.id_comp]
  simp only [Iso.trans_hom, Iso.symm_hom]
  rw [← Category.assoc, h, Category.assoc, hComparison]
  exact (Category.assoc _ _ _).symm

end PointedCGWH.Spectra.NativeStableMonoidal.SymmetricScalarSmash.Primitive

namespace PointedCGWH.Spectra.NativeStableMonoidal.SymmetricScalarSmash

private abbrev I := Operad.SmallFinBijGroupoid
private abbrev V := PointedCGWH.{u, v}
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

private abbrev A := PointedCGWH.sphereSequenceCommMon.{u, v}

private theorem A_eq_original : A.{u, v} = PointedCGWH.sphereSequenceCommMon.{u, v} := rfl

private abbrev E := NativeOmegaRecovery.NativeScalarCoefficient.coefficientOperatorEquivalence.{u, v}

private theorem E_eq_original :
    E.{u, v} = PointedCGWH.SymmetricModulePresentation.moduleOperatorEquivalence.{u, v} :=
  NativeOmegaRecovery.NativeScalarCoefficient.coefficientOperatorEquivalence_eq_original

open PointedCGWH.SymmetricModulePresentation
open NativeOmegaRecovery.NativeSymmetricFreeFunction
open NativeOmegaRecovery.NativeScalarCoefficient

attribute [local irreducible] moduleComparisonNat moduleOperatorComparison comparison

/-- The actual original module/operator comparison retains its whole coefficient source map and target pre-map. -/
private theorem recoverySource_eq (r : I) (T : V.{u, v}) :
    targetModuleFunctor r T ⋙ moduleToOperator.{u, v} =
      (moduleToOperator.{u, v} ⋙ PointedCGWH.SymmetricShift.functor r ⋙ cotensor T) ⋙
        operatorToModule.{u, v} ⋙ moduleToOperator.{u, v} := rfl

private def matchedRecovery (r : I) (T : V.{u, v}) :
    targetModuleFunctor r T ⋙ moduleToOperator.{u, v} ≅
      moduleToOperator.{u, v} ⋙ PointedCGWH.SymmetricShift.functor r ⋙ cotensor T :=
  eqToIso (recoverySource_eq r T) ≪≫ coefficientTargetRecoveryIso r T ≪≫
    Functor.rightUnitor
      (moduleToOperator.{u, v} ⋙ PointedCGWH.SymmetricShift.functor r ⋙ cotensor T)

private theorem matchedRecovery_hom_app (r : I) (T : V.{u, v})
    (N : OriginalModule.{u, v}) :
    (matchedRecovery r T).hom.app N = (coefficientTargetRecoveryIso r T).hom.app N := by
  have hEq : (eqToIso (recoverySource_eq r T)).hom.app N = 𝟙 _ := rfl
  simp only [matchedRecovery, Iso.trans_hom, NatTrans.comp_app,
    Functor.rightUnitor_hom_app, hEq, Category.id_comp]
  exact Category.comp_id _

private theorem matchedComparison_factors (r : I) (T : V.{u, v}) :
    (moduleOperatorComparison r T).hom =
      (Functor.isoWhiskerRight (moduleComparisonNat r T) moduleToOperator.{u, v}).hom ≫
        (matchedRecovery r T).hom := by
  apply NatTrans.ext
  funext N
  have h := congrArg (fun t => t.app N) (moduleOperatorComparison_coefficient_hom_factors r T)
  simp only [NatTrans.comp_app] at h
  dsimp only [coefficientOperatorEquivalence, NativeOmegaRecovery.ModuleCoefficientData.carrierEquivalence,
    moduleOperatorEquivalence] at h
  simpa only [NatTrans.comp_app, matchedRecovery_hom_app] using h

private theorem matchedRecovery_coefficient (r : I) {T T' : V.{u, v}} (p : T ⟶ T') :
    Functor.whiskerRight (targetModuleSourceNat r p) moduleToOperator.{u, v} ≫
      (matchedRecovery r T).hom =
    (matchedRecovery r T').hom ≫
      Functor.whiskerLeft moduleToOperator.{u, v}
        (Functor.whiskerLeft (PointedCGWH.SymmetricShift.functor r) (cotensorSourceNat p)) := by
  apply NatTrans.ext
  funext N
  have h := congrArg (fun t => t.app N) (targetModuleSourceNat_recovery_square r p)
  simpa only [NatTrans.comp_app, matchedRecovery_hom_app] using h

private theorem actualCarrierModuleSquare (r : I) {T T' : V.{u, v}} (p : T ⟶ T') :
    type_of% (NativeOmegaRecovery.FreeFunctionCarrierComparison.whiskerRight_coefficient
    moduleToOperator.{u, v}
    (FreeModuleSource.pre A.{u, v} (DayFreeCoefficient.freeSequenceMap r p))
    (moduleComparisonNat r T') (moduleComparisonNat r T) (targetModuleSourceNat r p)
    (moduleComparisonNat_coefficient r p)) :=
  NativeOmegaRecovery.FreeFunctionCarrierComparison.whiskerRight_coefficient
    moduleToOperator.{u, v}
    (FreeModuleSource.pre A.{u, v} (DayFreeCoefficient.freeSequenceMap r p))
    (moduleComparisonNat r T') (moduleComparisonNat r T) (targetModuleSourceNat r p)
    (moduleComparisonNat_coefficient r p)

/-- The original full module/operator comparison preserves every original coefficient map and target. -/
theorem moduleOperatorComparison_coefficient (r : I) {T T' : V.{u, v}} (p : T ⟶ T') :
    Functor.whiskerRight
        (FreeModuleSource.pre A.{u, v} (DayFreeCoefficient.freeSequenceMap r p)) moduleToOperator.{u, v} ≫
      (moduleOperatorComparison r T).hom =
    (moduleOperatorComparison r T').hom ≫
      Functor.whiskerLeft moduleToOperator.{u, v}
        (Functor.whiskerLeft (PointedCGWH.SymmetricShift.functor r) (cotensorSourceNat p)) := by
  exact Primitive.pasteSquares (W := OriginalModule.{u, v} ⥤ Carrier.{u, v})
    (matchedComparison_factors r T') (matchedComparison_factors r T)
    (actualCarrierModuleSquare r p) (matchedRecovery_coefficient r p)

end PointedCGWH.Spectra.NativeStableMonoidal.SymmetricScalarSmash
