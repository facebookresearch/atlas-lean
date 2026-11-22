/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.SymmetricFreeSourceFunctorTransport

/-!
# Transport of the complete coefficient-source comparison

The original source functor is transported before choosing a coefficient
object or arrow. Its target keeps the named original free-module pre-map.
-/

set_option autoImplicit false
noncomputable section

universe uC vC uP vP uD vD

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped MonoidalClosed CategoryTheory.MonObj

namespace PointedCGWH.Spectra.NativeStableMonoidal.SymmetricScalarSmash.WholeSource

variable {C : Type uC} [Category.{vC} C] [MonoidalCategory C] [BraidedCategory C]
  [MonoidalClosed C] [HasEqualizers C] [HasCoequalizers C]
  {P : Type uP} [Category.{vP} P] {D : Type uD} [Category.{vD} D]
  (A : CommMon C) (E : Mod C A.X ≌ D)

/-- The original balanced module tensor structure for the complete source comparison. -/
local instance moduleMonoidal : MonoidalCategory (Mod C A.X) := Mod.instMonoidalCategory A
/-- The original module internal Hom structure for the complete source comparison. -/
local instance moduleClosed : MonoidalClosed (Mod C A.X) := Mod.instMonoidalClosed A

/-- All coefficient objects and maps retain the full original free-module
internal Hom and its two original carrier whiskers. -/
def freeSourceTarget (K : P ⥤ C) : Pᵒᵖ ⥤ (D ⥤ D) :=
  { (K ⋙ Mod.free A.X).op ⋙ NativeOmegaPreparation.ModuleFunctionTransport.sourceFunctor A E with
    obj := fun T => E.inverse ⋙
      Mod.internalHom A ((Mod.free A.X).obj (K.obj T.unop)) ⋙ E.functor
    map := fun f => Functor.whiskerLeft E.inverse
      (Functor.whiskerRight (FreeModuleSource.pre A (K.map f.unop)) E.functor) }

/-- The named target preserves the whole original contravariant source functor. -/
theorem freeSourceTarget_eq_original (K : P ⥤ C) :
    freeSourceTarget A E K =
      (K ⋙ Mod.free A.X).op ⋙ NativeOmegaPreparation.ModuleFunctionTransport.sourceFunctor A E :=
  rfl

/-- Equality of the whole free functor identifies the complete source functor. -/
theorem freeSourceFunctor_eq (L : P ⥤ Mod C A.X) (K : P ⥤ C)
    (hL : L = K ⋙ Mod.free A.X) :
    L.op ⋙ NativeOmegaPreparation.ModuleFunctionTransport.sourceFunctor A E =
      freeSourceTarget A E K :=
  (congrArg
    (fun F : P ⥤ Mod C A.X =>
      F.op ⋙ NativeOmegaPreparation.ModuleFunctionTransport.sourceFunctor A E) hL).trans
    (freeSourceTarget_eq_original A E K).symm

/-- The whole equality comparison is constructed with its exact source
components, so no coefficient projection reduces a cast of entire functors. -/
def freeSourceTransport (L : P ⥤ Mod C A.X) (K : P ⥤ C)
    (hL : L = K ⋙ Mod.free A.X) :
    L.op ⋙ NativeOmegaPreparation.ModuleFunctionTransport.sourceFunctor A E ≅
      freeSourceTarget A E K :=
  NatIso.ofComponents
    (fun T => eqToIso (Functor.congr_obj (freeSourceFunctor_eq A E L K hL) T))
    (by
      intro T T' p
      have h := (eqToHom (freeSourceFunctor_eq A E L K hL)).naturality p
      simpa only [eqToIso.hom, eqToHom_app] using h)

/-- The component constructor preserves the entire equality isomorphism of
the original coefficient source functors. -/
theorem freeSourceTransport_eq_original (L : P ⥤ Mod C A.X) (K : P ⥤ C)
    (hL : L = K ⋙ Mod.free A.X) :
    freeSourceTransport A E L K hL = eqToIso (freeSourceFunctor_eq A E L K hL) := by
  apply Iso.ext
  apply NatTrans.ext
  funext T
  exact (eqToHom_app (freeSourceFunctor_eq A E L K hL) T).symm

/-- Every original coefficient arrow acts by the literal named free pre-map. -/
theorem freeSourceTarget_map (K : P ⥤ C) {T T' : P} (p : T ⟶ T') :
    (freeSourceTarget A E K).map p.op =
      Functor.whiskerLeft E.inverse
        (Functor.whiskerRight (FreeModuleSource.pre A (K.map p)) E.functor) :=
  rfl

/-- The full transported source comparison is natural in the complete
coefficient arrow and retains its original free pre-map. -/
theorem freeSourceTransport_coefficient (L : P ⥤ Mod C A.X) (K : P ⥤ C)
    (hL : L = K ⋙ Mod.free A.X) {T T' : P} (p : T ⟶ T') :
    (NativeOmegaPreparation.ModuleFunctionTransport.sourceFunctor A E).map (L.map p).op ≫
        (freeSourceTransport A E L K hL).hom.app (.op T) =
      (freeSourceTransport A E L K hL).hom.app (.op T') ≫
        Functor.whiskerLeft E.inverse
          (Functor.whiskerRight (FreeModuleSource.pre A (K.map p)) E.functor) :=
  (freeSourceTransport A E L K hL).hom.naturality p.op

/-- At the free recipe, the same entire component is the original equality
isomorphism between the two module-function source presentations. -/
theorem freeSourceTransport_app_recipe (K : P ⥤ C) (T : P) :
    (freeSourceTransport A E (K ⋙ Mod.free A.X) K rfl).app (.op T) =
      eqToIso (NativeOmegaPreparation.ModuleFunctionTransport.sourceFunctor_obj A E
        ((Mod.free A.X).obj (K.obj T))) := by
  apply Iso.ext
  apply NatTrans.ext
  funext X
  rfl

/-- Equal original coefficient maps retain their complete free pre-map and
both original carrier whiskers. -/
theorem whiskeredFreePre_congr {T T' : C} (p q : T ⟶ T') (h : p = q) :
    Functor.whiskerLeft E.inverse (Functor.whiskerRight (FreeModuleSource.pre A p) E.functor) =
      Functor.whiskerLeft E.inverse (Functor.whiskerRight (FreeModuleSource.pre A q) E.functor) :=
  congrArg
    (fun f : T ⟶ T' => Functor.whiskerLeft E.inverse
      (Functor.whiskerRight (FreeModuleSource.pre A f) E.functor)) h

/-- Equal actual module arrows have the same entire original function map. -/
theorem sourceFunctor_pre_congr {M M' : Mod C A.X} (p q : M ⟶ M') (h : p = q) :
    (NativeOmegaPreparation.ModuleFunctionTransport.sourceFunctor A E).map p.op =
      (NativeOmegaPreparation.ModuleFunctionTransport.sourceFunctor A E).map q.op :=
  congrArg
    (fun f : M ⟶ M' =>
      (NativeOmegaPreparation.ModuleFunctionTransport.sourceFunctor A E).map f.op) h

section Square
variable {W : Type uP} [Category.{vP} W]

/-- Identified whole comparison maps preserve the given entire source square. -/
theorem replaceSourceSquare
    {H H' G G' : W} {p : H ⟶ H'} {s s' : H' ⟶ G'}
    {e e' : H ⟶ G} {q q' : G ⟶ G'}
    (h : p ≫ s = e ≫ q) (hs : s = s') (he : e = e') (hq : q = q') :
    p ≫ s' = e' ≫ q' := by
  rw [← hs, ← he, ← hq]
  exact h

end Square

omit [MonoidalCategory C] [BraidedCategory C] [MonoidalClosed C]
  [HasEqualizers C] [HasCoequalizers C] in
/-- A whole original module square retains the composed carrier on its
target side and the exact original whiskered comparison isomorphisms. -/
theorem whiskerLeftSquare_flat (K : P ⥤ C) (L : C ⥤ D)
    {F F' : C ⥤ D} {R R' : D ⥤ D}
    (m : F ≅ L ⋙ R) (m' : F' ≅ L ⋙ R') (q : R ⟶ R')
    {p : F ⟶ F'} (h : p ≫ m'.hom = m.hom ≫ Functor.whiskerLeft L q) :
    Functor.whiskerLeft K p ≫ (Functor.isoWhiskerLeft K m').hom =
      (Functor.isoWhiskerLeft K m).hom ≫ Functor.whiskerLeft (K ⋙ L) q := by
  apply NatTrans.ext
  funext X
  exact NatTrans.congr_app h (K.obj X)






end PointedCGWH.Spectra.NativeStableMonoidal.SymmetricScalarSmash.WholeSource

universe u v

open CategoryTheory.EnrichedFunctorCat
open scoped MonoidalCategory MonoidalClosed CategoryTheory.MonObj

namespace PointedCGWH.Spectra.NativeStableMonoidal.SymmetricScalarSmash

private abbrev I := Operad.SmallFinBijGroupoid
private abbrev V := PointedCGWH.{u, v}
private abbrev S := PointedCGWH.sphereSequence.{u, v}
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

open PointedCGWH.SymmetricModulePresentation
open NativeOmegaRecovery.NativeSymmetricFreeFunction
open NativeOmegaRecovery.NativeScalarCoefficient

attribute [local irreducible] Mod.internalHom

/-- The original symmetric sphere-module tensor structure at the actual source. -/
local instance actualModuleMonoidal : MonoidalCategory (OriginalModule.{u, v}) :=
  Mod.instMonoidalCategory A.{u, v}
/-- The original symmetric sphere-module internal Hom structure at the actual source. -/
local instance actualModuleClosed : MonoidalClosed (OriginalModule.{u, v}) :=
  Mod.instMonoidalClosed A.{u, v}

private def actualWholeSourceFamily (r : I) : V.{u, v}ᵒᵖ ⥤ Carrier.{u, v} ⥤ Carrier.{u, v} :=
  (Mod.dayFreeAt S.{u, v} r).op ⋙
    NativeOmegaPreparation.ModuleFunctionTransport.sourceFunctor A.{u, v} E.{u, v}

private def actualWholeTargetFamily (r : I) : V.{u, v}ᵒᵖ ⥤ Carrier.{u, v} ⥤ Carrier.{u, v} :=
  WholeSource.freeSourceTarget A.{u, v} E.{u, v}
    (SymmetricFreeSourceFunctorTransport.coefficientSequenceFunctor r)

private def actualWholeSourceTransport (r : I) :
    actualWholeSourceFamily r ≅ actualWholeTargetFamily r :=
  WholeSource.freeSourceTransport A.{u, v} E.{u, v}
    (Mod.dayFreeAt S.{u, v} r)
    (SymmetricFreeSourceFunctorTransport.coefficientSequenceFunctor r)
    (SymmetricFreeSourceFunctorTransport.dayFree_eq_coefficientFree r)

private def actualOriginalSourceFactorFamily (r : I) :
    ∀ T : V.{u, v},
      (actualWholeSourceFamily r).obj (.op T) ≅ (actualWholeTargetFamily r).obj (.op T) :=
  comparisonSourceFactor r

private theorem actualOriginalSourceFactorFamily_whole (r : I) :
    HEq (actualOriginalSourceFactorFamily.{u, v} r) (comparisonSourceFactor.{u, v} r) :=
  HEq.refl _

/-- The exact component constructor retains the unchanged original source
comparison at every original coefficient and all native target inputs. -/
private theorem actualWholeSourceTransport_hom (r : I) (T : V.{u, v}) :
    (actualWholeSourceTransport r).hom.app (.op T) =
      (actualOriginalSourceFactorFamily r T).hom := by
  rfl

/-- Both original operator whiskers retain the literal original coefficient
map before it is substituted into the source square. -/
private theorem actualTargetPre_eq (r : I) {T T' : V.{u, v}} (p : T ⟶ T') :
    type_of% (WholeSource.whiskeredFreePre_congr A.{u, v} E.{u, v}
      ((SymmetricFreeSourceFunctorTransport.coefficientSequenceFunctor r).map p)
      (DayFreeCoefficient.freeSequenceMap r p)
      (SymmetricFreeSourceFunctorTransport.coefficientSequenceFunctor_map r p)) :=
  WholeSource.whiskeredFreePre_congr A.{u, v} E.{u, v}
    ((SymmetricFreeSourceFunctorTransport.coefficientSequenceFunctor r).map p)
    (DayFreeCoefficient.freeSequenceMap r p)
    (SymmetricFreeSourceFunctorTransport.coefficientSequenceFunctor_map r p)

set_option maxHeartbeats 1000000 in
-- Paste the entire original native source square through the checked component equalities.
/-- Every actual original coefficient arrow preserves the whole original
source factor and its unchanged homogeneous free-coefficient pre-map. -/
theorem comparisonSourceFactor_coefficient (r : I) {T T' : V.{u, v}} (p : T ⟶ T') :
    NativeOmegaPreparation.SymmetricFunction.precompose (n := r) (k := r) (M := T') (N := T)
        ((Mod.dayFreeAt S.{u, v} r).map p) ≫
      (comparisonSourceFactor r T).hom =
    (comparisonSourceFactor r T').hom ≫
      Functor.whiskerLeft operatorToModule.{u, v}
        (Functor.whiskerRight
          (FreeModuleSource.pre A.{u, v} (DayFreeCoefficient.freeSequenceMap r p))
          moduleToOperator.{u, v}) := by
  have h := WholeSource.freeSourceTransport_coefficient A.{u, v} E.{u, v}
    (Mod.dayFreeAt S.{u, v} r)
    (SymmetricFreeSourceFunctorTransport.coefficientSequenceFunctor r)
    (SymmetricFreeSourceFunctorTransport.dayFree_eq_coefficientFree r) p
  exact WholeSource.replaceSourceSquare (W := Carrier.{u, v} ⥤ Carrier.{u, v}) h
    (actualWholeSourceTransport_hom r T) (actualWholeSourceTransport_hom r T')
    (actualTargetPre_eq r p)





attribute [local irreducible] moduleComparisonNat moduleOperatorComparison comparison

set_option maxHeartbeats 500000 in
-- Use the checked whole-whisker constructor at the original module-factor endpoints.
private theorem comparisonModuleFactor_coefficient (r : I) {T T' : V.{u, v}} (p : T ⟶ T') :
    Functor.whiskerLeft operatorToModule.{u, v}
        (Functor.whiskerRight
          (FreeModuleSource.pre A.{u, v} (DayFreeCoefficient.freeSequenceMap r p))
          moduleToOperator.{u, v}) ≫
      (comparisonModuleFactor r T).hom =
    (comparisonModuleFactor r T').hom ≫
      Functor.whiskerLeft (operatorToModule.{u, v} ⋙ moduleToOperator.{u, v})
        (Functor.whiskerLeft (PointedCGWH.SymmetricShift.functor r) (cotensorSourceNat p)) :=
  WholeSource.whiskerLeftSquare_flat operatorToModule.{u, v} moduleToOperator.{u, v}
    (moduleOperatorComparison r T') (moduleOperatorComparison r T)
    (Functor.whiskerLeft (PointedCGWH.SymmetricShift.functor r) (cotensorSourceNat p))
    (moduleOperatorComparison_coefficient r p)





private theorem comparisonRecoveryFactor_coefficient (r : I) {T T' : V.{u, v}} (p : T ⟶ T') :
    Functor.whiskerLeft (operatorToModule.{u, v} ⋙ moduleToOperator.{u, v})
        (Functor.whiskerLeft (PointedCGWH.SymmetricShift.functor r) (cotensorSourceNat p)) ≫
      (comparisonRecoveryFactor r T).hom =
    (comparisonRecoveryFactor r T').hom ≫
      Functor.whiskerLeft (PointedCGWH.SymmetricShift.functor r) (cotensorSourceNat p) := by
  apply NatTrans.ext
  funext X
  let q := Functor.whiskerLeft (PointedCGWH.SymmetricShift.functor r) (cotensorSourceNat p)
  exact (q.naturality (E.{u, v}.counitIso.hom.app X)).symm

set_option maxHeartbeats 500000 in
-- Preserve all three actual native factor types while pasting their whole coefficient squares.
/-- Every original coefficient pre-map preserves all three whole factors
of the original function comparison. -/
theorem originalComparison_coefficient (r : I) {T T' : V.{u, v}} (p : T ⟶ T') :
    NativeOmegaPreparation.SymmetricFunction.precompose (n := r) (k := r) (M := T') (N := T)
        ((Mod.dayFreeAt S.{u, v} r).map p) ≫
      (comparison r T).hom =
    (comparison r T').hom ≫
      Functor.whiskerLeft (PointedCGWH.SymmetricShift.functor r) (cotensorSourceNat p) :=
  Primitive.coefficientOfFactors (W := Carrier.{u, v} ⥤ Carrier.{u, v})
    (comparisonSourceFactor r T') (comparisonSourceFactor r T)
    (comparisonModuleFactor r T') (comparisonModuleFactor r T)
    (comparisonRecoveryFactor r T') (comparisonRecoveryFactor r T)
    (comparison r T') (comparison r T) (comparison_factorization r T') (comparison_factorization r T)
    (comparisonSourceFactor_coefficient r p) (comparisonModuleFactor_coefficient r p)
    (comparisonRecoveryFactor_coefficient r p)

private theorem nativeFreeComparison_hom_factor (r : I) (T : V.{u, v}) :
    (nativeFreeComparison r T).hom =
      ((NativeOmegaPreparation.NativeSymmetricFunction.originalFreeComparison r T).symm ≪≫
        comparison r T).hom := rfl

private theorem sourceArrow_precompose_coefficient (r : I) {T T' : V.{u, v}} (p : T ⟶ T') :
    type_of% (WholeSource.sourceFunctor_pre_congr A.{u, v} E.{u, v}
      (NativeOmegaRecovery.NativeSymmetricFreeSource.sourceArrow
        (Free.coefficientMap (PointedCGWH.symmetricOperatorObj r) p))
      ((Mod.dayFreeAt S.{u, v} r).map p)
      (NativeOmegaRecovery.NativeSymmetricFreeFunction.sourceArrow_coefficient r p)) :=
  WholeSource.sourceFunctor_pre_congr A.{u, v} E.{u, v}
    (NativeOmegaRecovery.NativeSymmetricFreeSource.sourceArrow
      (Free.coefficientMap (PointedCGWH.symmetricOperatorObj r) p))
    ((Mod.dayFreeAt S.{u, v} r).map p)
    (NativeOmegaRecovery.NativeSymmetricFreeFunction.sourceArrow_coefficient r p)

private theorem cotensorSourceNat_eq_original {T T' : V.{u, v}} (p : T ⟶ T') :
    cotensorSourceNat p =
      (ScalarLeibniz.cotensorBifunctor (A := PointedCGWH.SymmetricOperatorIndex.{u, v})).map p.op := by
  apply NatTrans.ext
  funext X
  rfl

private theorem shiftedCotensorSourceNat_eq_original (r : I) {T T' : V.{u, v}} (p : T ⟶ T') :
    Functor.whiskerLeft (PointedCGWH.SymmetricShift.functor r) (cotensorSourceNat p) =
      Functor.whiskerLeft (PointedCGWH.SymmetricShift.functor r)
        ((ScalarLeibniz.cotensorBifunctor (A := PointedCGWH.SymmetricOperatorIndex.{u, v})).map p.op) :=
  congrArg (Functor.whiskerLeft (PointedCGWH.SymmetricShift.functor r))
    (cotensorSourceNat_eq_original p)

set_option maxHeartbeats 500000 in
-- Retain both entire original free-source comparisons and the actual native coefficient arrow.
/-- The original full native free-function comparison is natural in every
original coefficient arrow. -/
theorem nativeFreeComparison_coefficient (r : I) {T T' : V.{u, v}} (p : T ⟶ T') :
    NativeOmegaPreparation.NativeSymmetricFunction.precompose
        (Free.coefficientMap (PointedCGWH.symmetricOperatorObj r) p) ≫
      (nativeFreeComparison r T).hom =
    (nativeFreeComparison r T').hom ≫
      Functor.whiskerLeft (PointedCGWH.SymmetricShift.functor r)
        ((ScalarLeibniz.cotensorBifunctor (A := PointedCGWH.SymmetricOperatorIndex.{u, v})).map p.op) := by
  let f := Free.coefficientMap (PointedCGWH.symmetricOperatorObj r) p
  have hFree := WholeSource.replaceSourceSquare (W := Carrier.{u, v} ⥤ Carrier.{u, v})
    (NativeOmegaRecovery.NativeSymmetricFreeSource.originalFreeComparison_precompose f)
    rfl (sourceArrow_precompose_coefficient r p) rfl
  have h := Primitive.inverseSourceCoefficient (W := Carrier.{u, v} ⥤ Carrier.{u, v})
    (NativeOmegaPreparation.NativeSymmetricFunction.originalFreeComparison r T')
    (NativeOmegaPreparation.NativeSymmetricFunction.originalFreeComparison r T)
    (comparison r T') (comparison r T) hFree (originalComparison_coefficient r p)
  exact WholeSource.replaceSourceSquare (W := Carrier.{u, v} ⥤ Carrier.{u, v}) h
    (nativeFreeComparison_hom_factor r T).symm (nativeFreeComparison_hom_factor r T').symm
    (shiftedCotensorSourceNat_eq_original r p)






end PointedCGWH.Spectra.NativeStableMonoidal.SymmetricScalarSmash
