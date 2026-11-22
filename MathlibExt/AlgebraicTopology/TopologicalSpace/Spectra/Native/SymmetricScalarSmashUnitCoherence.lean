/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.SymmetricScalarSmash
import MathlibExt.AlgebraicTopology.Spectra.Symmetric.PointedCGWH.FunctionSpectrum.LambdaAdjunction
import MathlibExt.AlgebraicTopology.Spectra.Symmetric.PointedCGWH.FunctionSpectrum.NativeSelectedUnitMate

/-!
# The original symmetric scalar unit and right tensor

The scalar comparison at the pointed unit is identified with the chosen
original free-zero smash unit by its entire adjunction mate. The original
balanced unit contraction supplies the right tensor coherence.
-/

set_option autoImplicit false
noncomputable section

universe u v uC vC uD vD

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open CategoryTheory.EnrichedFunctorCat
open scoped MonoidalCategory MonoidalClosed

namespace PointedCGWH.Spectra.NativeStableMonoidal.SymmetricScalarSmash.UnitCoherence

private theorem functorUnitExchange {C : Type uC} [Category.{vC} C] {F S K : C ⥤ C}
    (e : F ≅ S ⋙ K) (r : S ≅ 𝟭 C) (q : K ≅ 𝟭 C) :
    (e ≪≫ Functor.isoWhiskerRight r K ≪≫ Functor.leftUnitor K) ≪≫ q =
      (e ≪≫ Functor.isoWhiskerLeft S q ≪≫ Functor.rightUnitor S) ≪≫ r := by
  apply Iso.ext
  apply NatTrans.ext
  funext X
  have h := q.hom.naturality (r.hom.app X)
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.leftUnitor_hom_app, Functor.rightUnitor_hom_app]
  simp only [Functor.comp_obj, Functor.id_obj, Category.comp_id, Category.assoc]
  simpa only [Functor.id_obj, Functor.id_map, Category.assoc] using
    congrArg (fun f => e.hom.app X ≫ f) h

private theorem comparisonUnitIso {C : Type uC} [Category.{vC} C] {F S R K : C ⥤ C}
    (a : F ⊣ R) (b : S ⊣ K) (r : R ≅ K) (q : K ≅ 𝟭 C) (e : S ≅ 𝟭 C)
    (hScalar : ∀ X : C, b.homEquiv X X (e.hom.app X) = q.inv.app X) :
    (a.ofNatIsoRight r).leftAdjointUniq b ≪≫ e =
      CategoryTheory.FunctionUnitAdjunction.leftUnitIso a (r ≪≫ q) := by
  apply Iso.ext
  apply NatTrans.ext
  funext X
  let c := a.ofNatIsoRight r
  let f := e.hom.app X
  have hNat := c.homEquiv_naturality_right ((c.leftAdjointUniq b).hom.app X) f
  have hUnit := Adjunction.homEquiv_leftAdjointUniq_hom_app c b X
  have hForward : c.homEquiv X X ((c.leftAdjointUniq b).hom.app X ≫ f) =
      b.homEquiv X X f :=
    hNat.trans ((congrArg (fun z => z ≫ K.map f) hUnit).trans
      (b.homEquiv_unit X X f).symm)
  have hLeft : a.homEquiv X X ((c.leftAdjointUniq b).hom.app X ≫ f) =
      (r ≪≫ q).inv.app X := by
    apply (cancel_mono (r.hom.app X)).mp
    have h := (Adjunction.homEquiv_ofNatIsoRight_apply a r
      ((c.leftAdjointUniq b).hom.app X ≫ f)).symm.trans (hForward.trans (hScalar X))
    refine h.trans ?_
    simp only [Iso.trans_inv, NatTrans.comp_app, Category.assoc,
      Iso.inv_hom_id_app, Category.comp_id]
  apply (a.homEquiv X X).injective
  exact hLeft.trans
    (CategoryTheory.FunctionUnitAdjunction.unitInverse_adjoint a (r ≪≫ q) X).symm

private theorem interchangeUnit {C : Type uC} [Category.{vC} C] [MonoidalCategory C]
    (A : C) (S : C ⥤ C) (e : MonoidalCategory.tensorLeft A ≅ S) (X Y : C)
    (tX : S.obj X ⟶ X) (tXY : S.obj (X ⊗ Y) ⟶ X ⊗ Y)
    (h : (α_ A X Y).inv ≫ ((e.hom.app X ≫ tX) ▷ Y) = e.hom.app (X ⊗ Y) ≫ tXY) :
    (CategoryTheory.TensorRepresentedInterchange.interchange A S e X Y).hom ≫ (tX ▷ Y) = tXY := by
  have h' := congrArg (fun f => e.inv.app (X ⊗ Y) ≫ f) h
  change (e.inv.app (X ⊗ Y) ≫ (α_ A X Y).inv ≫ (e.hom.app X ▷ Y)) ≫ (tX ▷ Y) = tXY
  simpa only [comp_whiskerRight, Category.assoc, Iso.inv_hom_id_app_assoc] using h'

/-- The entire transported left-tensor functor is the original smash functor. -/
private theorem transportedTensorLeft_eq_source
    {C : Type uC} [Category.{vC} C] [MonoidalCategory C] [BraidedCategory C]
    [MonoidalClosed C] [HasCoequalizers C] (A : CommMon C)
    {D : Type uD} [Category.{vD} D] (E : Mod C A.X ≌ D) (S : D) :
    letI : MonoidalCategory (Mod C A.X) := Mod.instMonoidalCategory A
    letI : MonoidalCategory D := Monoidal.transport E
    MonoidalCategory.tensorLeft S = Mod.EquivalenceFunctionTransport.smashFunctor A E S := rfl

/-- The actual transported tensor/source equality is retained before either
selected unit component is read. -/
private theorem selectedUnitActionWithSourceCast
    {C : Type uC} [Category.{vC} C] [MonoidalCategory C] [BraidedCategory C]
    [MonoidalClosed C] [HasCoequalizers C] [HasEqualizers C] (A : CommMon C)
    {D : Type uD} [Category.{vD} D] (E : Mod C A.X ≌ D)
    (M : Mod C A.X) (S : D) (eS : M ≅ E.inverse.obj S) (t : M ⟶ Mod.regular A.X)
    {R : D ⥤ D} (e : Mod.internalHom A M ≅ E.functor ⋙ R ⋙ E.inverse)
    (uR : R ≅ 𝟭 D)
    (h : ∀ N : Mod C A.X,
      (NativeOmegaRecovery.SelectedUnitTensorCompatibility.contractionCurrySource A M t).app N ≫
          e.hom.app N = E.unitIso.hom.app N ≫ E.inverse.map (uR.inv.app (E.functor.obj N)))
    (X : D) :
    letI : MonoidalCategory (Mod C A.X) := Mod.instMonoidalCategory A
    letI : MonoidalCategory D := Monoidal.transport E
    let k : MonoidalCategory.tensorLeft S ≅ Mod.EquivalenceFunctionTransport.smashFunctor A E S :=
      eqToIso (transportedTensorLeft_eq_source A E S)
    let l := CategoryTheory.FunctionUnitAdjunction.leftUnitIso
      (Mod.EquivalenceFunctionTransport.adjunction A E S)
      (NativeOmegaRecovery.NativeSelectedUnitTransport.selectedSourceUnit A E M S eS e uR)
    k.hom.app X ≫ l.hom.app X =
      ((((ρ_ S).inv ≫ (k.hom.app (𝟙_ D) ≫ l.hom.app (𝟙_ D))) ▷ X) ≫ (λ_ X).hom) := by
  let _ : MonoidalCategory (Mod C A.X) := Mod.instMonoidalCategory A
  let _ : MonoidalCategory D := Monoidal.transport E
  let k : MonoidalCategory.tensorLeft S ≅ Mod.EquivalenceFunctionTransport.smashFunctor A E S :=
    eqToIso (transportedTensorLeft_eq_source A E S)
  let l := CategoryTheory.FunctionUnitAdjunction.leftUnitIso
    (Mod.EquivalenceFunctionTransport.adjunction A E S)
    (NativeOmegaRecovery.NativeSelectedUnitTransport.selectedSourceUnit A E M S eS e uR)
  change k.hom.app X ≫ l.hom.app X =
    ((((ρ_ S).inv ≫ (k.hom.app (𝟙_ D) ≫ l.hom.app (𝟙_ D))) ▷ X) ≫ (λ_ X).hom)
  have hk : k.hom = 𝟙 (MonoidalCategory.tensorLeft S) := rfl
  have hCastX : k.hom.app X ≫ l.hom.app X = l.hom.app X := by
    exact (congrArg (fun f => f ≫ l.hom.app X) (NatTrans.congr_app hk X)).trans
      (Category.id_comp _)
  have hCastUnit : (k.hom.app (𝟙_ D) ≫ l.hom.app (𝟙_ D)) = l.hom.app (𝟙_ D) := by
    exact (congrArg (fun f => f ≫ l.hom.app (𝟙_ D)) (NatTrans.congr_app hk (𝟙_ D))).trans
      (Category.id_comp _)
  have hAction := NativeOmegaRecovery.NativeSelectedUnitTransport.selectedSourceUnit_selected_action
    A E M S eS t e uR h X
  have hRight := congrArg (fun f => (((ρ_ S).inv ≫ f) ▷ X) ≫ (λ_ X).hom) hCastUnit
  exact hCastX.trans (hAction.trans hRight.symm)

/-- Equality with the original transported monoidal record is eliminated
before any tensor-source or selected-unit component is formed. -/
private theorem tensorLeft_eq_source_ofMonoidalEquality
    {C : Type uC} [Category.{vC} C] [MonoidalCategory C] [BraidedCategory C]
    [MonoidalClosed C] [HasCoequalizers C] (A : CommMon C)
    {D : Type uD} [Category.{vD} D] (E : Mod C A.X ≌ D)
    (mD : MonoidalCategory D)
    (hMonoidal : letI : MonoidalCategory (Mod C A.X) := Mod.instMonoidalCategory A
      mD = Monoidal.transport E) (S : D) :
    letI : MonoidalCategory (Mod C A.X) := Mod.instMonoidalCategory A
    letI : MonoidalCategory D := mD
    MonoidalCategory.tensorLeft S = Mod.EquivalenceFunctionTransport.smashFunctor A E S := by
  cases hMonoidal
  exact transportedTensorLeft_eq_source A E S

private theorem selectedUnitActionWithMonoidalEquality
    {C : Type uC} [Category.{vC} C] [MonoidalCategory C] [BraidedCategory C]
    [MonoidalClosed C] [HasCoequalizers C] [HasEqualizers C] (A : CommMon C)
    {D : Type uD} [Category.{vD} D] (E : Mod C A.X ≌ D)
    (mD : MonoidalCategory D)
    (hMonoidal : letI : MonoidalCategory (Mod C A.X) := Mod.instMonoidalCategory A
      mD = Monoidal.transport E)
    (M : Mod C A.X) (S : D) (eS : M ≅ E.inverse.obj S) (t : M ⟶ Mod.regular A.X)
    {R : D ⥤ D} (e : Mod.internalHom A M ≅ E.functor ⋙ R ⋙ E.inverse)
    (uR : R ≅ 𝟭 D)
    (h : ∀ N : Mod C A.X,
      (NativeOmegaRecovery.SelectedUnitTensorCompatibility.contractionCurrySource A M t).app N ≫
          e.hom.app N = E.unitIso.hom.app N ≫ E.inverse.map (uR.inv.app (E.functor.obj N)))
    (X : D) :
    letI : MonoidalCategory (Mod C A.X) := Mod.instMonoidalCategory A
    letI : MonoidalCategory D := mD
    let k : MonoidalCategory.tensorLeft S ≅ Mod.EquivalenceFunctionTransport.smashFunctor A E S :=
      eqToIso (tensorLeft_eq_source_ofMonoidalEquality A E mD hMonoidal S)
    let l := CategoryTheory.FunctionUnitAdjunction.leftUnitIso
      (Mod.EquivalenceFunctionTransport.adjunction A E S)
      (NativeOmegaRecovery.NativeSelectedUnitTransport.selectedSourceUnit A E M S eS e uR)
    k.hom.app X ≫ l.hom.app X =
      ((((ρ_ S).inv ≫ (k.hom.app (𝟙_ D) ≫ l.hom.app (𝟙_ D))) ▷ X) ≫ (λ_ X).hom) := by
  let _ : MonoidalCategory (Mod C A.X) := Mod.instMonoidalCategory A
  cases hMonoidal
  exact selectedUnitActionWithSourceCast A E M S eS t e uR h X

/-- The complete original source-unit recipe is named before specializing
its module and carrier data. -/
private def sourceUnitIsoFactory
    {C : Type uC} [Category.{vC} C] [MonoidalCategory C] [BraidedCategory C]
    [MonoidalClosed C] [HasCoequalizers C] [HasEqualizers C] (A : CommMon C)
    {D : Type uD} [Category.{vD} D] (E : Mod C A.X ≌ D)
    (mD : MonoidalCategory D)
    (hMonoidal : letI : MonoidalCategory (Mod C A.X) := Mod.instMonoidalCategory A
      mD = Monoidal.transport E)
    (M : Mod C A.X) (S : D) (eS : M ≅ E.inverse.obj S)
    {R : D ⥤ D} (e : Mod.internalHom A M ≅ E.functor ⋙ R ⋙ E.inverse) (uR : R ≅ 𝟭 D) :
    letI : MonoidalCategory (Mod C A.X) := Mod.instMonoidalCategory A
    letI : MonoidalCategory D := mD
    MonoidalCategory.tensorLeft S ≅ 𝟭 D := by
  letI : MonoidalCategory (Mod C A.X) := Mod.instMonoidalCategory A
  letI : MonoidalCategory D := mD
  exact eqToIso (tensorLeft_eq_source_ofMonoidalEquality A E mD hMonoidal S) ≪≫
    CategoryTheory.FunctionUnitAdjunction.leftUnitIso
      (Mod.EquivalenceFunctionTransport.adjunction A E S)
      (NativeOmegaRecovery.NativeSelectedUnitTransport.selectedSourceUnit A E M S eS e uR)

/-- The complete factory has the unchanged original tensor/source and selected-unit recipe. -/
private theorem sourceUnitIsoFactory_recipe
    {C : Type uC} [Category.{vC} C] [MonoidalCategory C] [BraidedCategory C]
    [MonoidalClosed C] [HasCoequalizers C] [HasEqualizers C] (A : CommMon C)
    {D : Type uD} [Category.{vD} D] (E : Mod C A.X ≌ D)
    (mD : MonoidalCategory D)
    (hMonoidal : letI : MonoidalCategory (Mod C A.X) := Mod.instMonoidalCategory A
      mD = Monoidal.transport E)
    (M : Mod C A.X) (S : D) (eS : M ≅ E.inverse.obj S)
    {R : D ⥤ D} (e : Mod.internalHom A M ≅ E.functor ⋙ R ⋙ E.inverse) (uR : R ≅ 𝟭 D) :
    letI : MonoidalCategory (Mod C A.X) := Mod.instMonoidalCategory A
    letI : MonoidalCategory D := mD
    sourceUnitIsoFactory A E mD hMonoidal M S eS e uR =
      eqToIso (tensorLeft_eq_source_ofMonoidalEquality A E mD hMonoidal S) ≪≫
        CategoryTheory.FunctionUnitAdjunction.leftUnitIso
          (Mod.EquivalenceFunctionTransport.adjunction A E S)
          (NativeOmegaRecovery.NativeSelectedUnitTransport.selectedSourceUnit A E M S eS e uR) := rfl

/-- The genuine whole original module mate gives the action of that same
named source-unit construction on every carrier object. -/
private theorem sourceUnitIsoFactory_action
    {C : Type uC} [Category.{vC} C] [MonoidalCategory C] [BraidedCategory C]
    [MonoidalClosed C] [HasCoequalizers C] [HasEqualizers C] (A : CommMon C)
    {D : Type uD} [Category.{vD} D] (E : Mod C A.X ≌ D)
    (mD : MonoidalCategory D)
    (hMonoidal : letI : MonoidalCategory (Mod C A.X) := Mod.instMonoidalCategory A
      mD = Monoidal.transport E)
    (M : Mod C A.X) (S : D) (eS : M ≅ E.inverse.obj S) (t : M ⟶ Mod.regular A.X)
    {R : D ⥤ D} (e : Mod.internalHom A M ≅ E.functor ⋙ R ⋙ E.inverse) (uR : R ≅ 𝟭 D)
    (h : ∀ N : Mod C A.X,
      (NativeOmegaRecovery.SelectedUnitTensorCompatibility.contractionCurrySource A M t).app N ≫
          e.hom.app N = E.unitIso.hom.app N ≫ E.inverse.map (uR.inv.app (E.functor.obj N)))
    (X : D) :
    letI : MonoidalCategory (Mod C A.X) := Mod.instMonoidalCategory A
    letI : MonoidalCategory D := mD
    (sourceUnitIsoFactory A E mD hMonoidal M S eS e uR).hom.app X =
      ((((ρ_ S).inv ≫ (sourceUnitIsoFactory A E mD hMonoidal M S eS e uR).hom.app (𝟙_ D)) ▷ X) ≫
        (λ_ X).hom) := by
  let _ : MonoidalCategory (Mod C A.X) := Mod.instMonoidalCategory A
  let _ : MonoidalCategory D := mD
  have hAction := selectedUnitActionWithMonoidalEquality A E mD hMonoidal M S eS t e uR h X
  simpa only [sourceUnitIsoFactory, Iso.trans_hom, NatTrans.comp_app] using hAction

/-- The complete target equality identifies two original equality comparisons. -/
private theorem eqToIso_heq_of_target_eq
    {C : Type uC} [Category.{vC} C] {F G G' : C}
    (hG : G = G') (h : F = G) (h' : F = G') : HEq (eqToIso h) (eqToIso h') := by
  cases hG
  cases Subsingleton.elim h h'
  rfl

/-- The whole intermediate object and both whole comparison values are
identified before composing the original isomorphisms. -/
private theorem isoTrans_eq_of_middle_heq
    {C : Type uC} [Category.{vC} C] {F G G' K : C}
    (hG : G = G') (a : F ≅ G) (a' : F ≅ G') (ha : HEq a a')
    (b : G ≅ K) (b' : G' ≅ K) (hb : HEq b b') : a ≪≫ b = a' ≪≫ b' := by
  cases hG
  cases ha
  cases hb
  rfl

/-- The whole tensor-source equality is eliminated before the original
unit presentation is projected to its forward map. -/
private theorem tensorUnitPresentation_hom
    {C : Type uC} [Category.{vC} C] [MonoidalCategory C]
    (S : C) (F : C ⥤ C) (hF : MonoidalCategory.tensorLeft S = F)
    (hUnit : S ⊗ (𝟙_ C) = F.obj (𝟙_ C)) (e : F ≅ 𝟭 C) :
    ((ρ_ S).symm ≪≫ eqToIso hUnit ≪≫ e.app (𝟙_ C)).hom =
      (ρ_ S).inv ≫ (eqToIso hF ≪≫ e).hom.app (𝟙_ C) := by
  cases hF
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.app_hom,
    eqToIso_refl, Iso.refl_hom, Category.id_comp]

attribute [local instance] Operad.SmallFinBijGroupoid.instMonoidalCategory
  Operad.SmallFinBijGroupoid.instSymmetricCategory
  PointedCGWH.copowerUnderlyingEnrichedOrdinary PointedCGWH.copowerUnderlyingMonoidal
  PointedCGWH.sphereSequenceMonObj PointedCGWH.sphereSequenceIsCommMonObj
  PointedCGWH.EnrichedMapping.hasSmallLimits
  NativeOmegaPreparation.SymmetricFunction.sequenceCoequalizers
  NativeOmegaPreparation.SymmetricFunction.sequenceEqualizers
  PointedCGWH.Spectra.NativeStableMonoidal.SymmetricSmash.monoidalCategory
  PointedCGWH.Spectra.NativeStableMonoidal.SymmetricSmash.symmetricCategory
  PointedCGWH.Spectra.NativeStableMonoidal.SymmetricSmash.monoidalClosed


/-- The actual scalar comparison followed by the original scalar left unit. -/
def unitIso (X : Carrier.{u, v}) : zeroFree.{u, v} (𝟙_ PointedCGWH.{u, v}) ⊗ X ≅ X :=
  (tensorScalarIso.{u, v} (𝟙_ PointedCGWH.{u, v})).app X ≪≫ scalarUnitIso X

/-- The full function scalar comparison at the unit recovers the chosen
original free-function unit comparison. -/
theorem functionScalarIso_unit :
    functionScalarIso.{u, v} (𝟙_ PointedCGWH.{u, v}) ≪≫
        NativeOmegaRecovery.OriginalCotensorUnit.comparison =
      NativeOmegaRecovery.NativeSymmetricFreeFunction.nativeUnitComparison.{u, v} := by
  unfold functionScalarIso NativeOmegaRecovery.NativeSymmetricFreeFunction.nativeUnitComparison
    NativeOmegaRecovery.NativeSymmetricFreeFunction.nativeFreeUnitComparison
  exact functorUnitExchange
      (NativeOmegaRecovery.NativeSymmetricFreeFunction.nativeFreeComparison.{u, v}
        (𝟙_ Operad.SmallFinBijGroupoid) (𝟙_ PointedCGWH.{u, v}))
      NativeOmegaRecovery.NativeSymmetricShiftUnit.comparison.{u, v}
      (NativeOmegaRecovery.OriginalCotensorUnit.comparison (V := PointedCGWH.{u, v})
        (J := PointedCGWH.SymmetricOperatorIndex.{u, v}))

private def scalarUnitFunctorIso :
    EnrichedFunctorCat.tensorLeft (A := PointedCGWH.SymmetricOperatorIndex.{u, v})
      (𝟙_ PointedCGWH.{u, v}) ≅ 𝟭 Carrier.{u, v} :=
  NatIso.ofComponents (fun X => scalarUnitIso X) (fun f => scalarUnitIso_naturality f)

/-- The entire scalar-unit composite is the original chosen free-zero
smash unit, using both full original adjunctions. -/
theorem originalSmashScalarIso_unit :
    originalSmashScalarIso.{u, v} (𝟙_ PointedCGWH.{u, v}) ≪≫ scalarUnitFunctorIso.{u, v} =
      SymmetricSmash.freeZeroSmashUnitIso.{u, v} := by
  have hScalar : ∀ X : Carrier.{u, v},
      (ScalarLeibniz.adjunction (A := PointedCGWH.SymmetricOperatorIndex.{u, v})
        (𝟙_ PointedCGWH.{u, v})).homEquiv X X (scalarUnitFunctorIso.hom.app X) =
          NativeOmegaRecovery.OriginalCotensorUnit.comparison.inv.app X := by
    intro X
    exact ScalarLeibniz.adjunction_homEquiv_apply (𝟙_ PointedCGWH.{u, v}) X X (scalarUnitIso X).hom
  have h := comparisonUnitIso
    (NativeOmegaPreparation.NativeSymmetricFunction.adjunction
      (zeroFree.{u, v} (𝟙_ PointedCGWH.{u, v})))
    (ScalarLeibniz.adjunction (A := PointedCGWH.SymmetricOperatorIndex.{u, v})
      (𝟙_ PointedCGWH.{u, v}))
    (functionScalarIso.{u, v} (𝟙_ PointedCGWH.{u, v}))
    (NativeOmegaRecovery.OriginalCotensorUnit.comparison (V := PointedCGWH.{u, v})
      (J := PointedCGWH.SymmetricOperatorIndex.{u, v}))
    scalarUnitFunctorIso.{u, v} hScalar
  rw [functionScalarIso_unit] at h
  simpa only [originalSmashScalarIso, zeroFree,
    CategoryTheory.FunctionUnitAdjunction.leftUnitIso,
    SymmetricSmash.freeZeroSmashUnitIso] using h

/-- The whole original tensor source equality is retained before selecting
any scalar-unit component. -/
theorem unitIso_hom_original (X : Carrier.{u, v}) :
    (unitIso X).hom =
      (eqToIso (SymmetricSmash.tensorLeft_eq_originalSmash
        (zeroFree.{u, v} (𝟙_ PointedCGWH.{u, v}))) ≪≫
        SymmetricSmash.freeZeroSmashUnitIso.{u, v}).hom.app X := by
  have h : tensorScalarIso.{u, v} (𝟙_ PointedCGWH.{u, v}) ≪≫ scalarUnitFunctorIso.{u, v} =
      eqToIso (SymmetricSmash.tensorLeft_eq_originalSmash
        (zeroFree.{u, v} (𝟙_ PointedCGWH.{u, v}))) ≪≫
          SymmetricSmash.freeZeroSmashUnitIso.{u, v} := by
    unfold tensorScalarIso
    rw [Iso.trans_assoc, originalSmashScalarIso_unit]
  exact congrArg (fun e => e.hom.app X) h

attribute [local instance] NativeOmegaPreparation.SymmetricFunction.sequenceClosed
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

attribute [local irreducible] Mod.internalHom
  CategoryTheory.MonoidalCategory.DayFunctor.inst
  CategoryTheory.MonoidalCategory.DayFunctor.instBraidedCategory

private abbrev Coefficient : CommMon PointedCGWH.SymmetricSequence.{u, v} where
  X := PointedCGWH.sphereSequence.{u, v}
  mon := PointedCGWH.sphereSequenceMonObj.{u, v}
  comm := PointedCGWH.sphereSequenceIsCommMonObj.{u, v}

private theorem Coefficient_eq_original : Coefficient.{u, v} = PointedCGWH.sphereSequenceCommMon.{u, v} := rfl

private abbrev ModuleEquivalence :
    Mod PointedCGWH.SymmetricSequence.{u, v} PointedCGWH.sphereSequence.{u, v} ≌
      HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK.Actual.SymmetricCarrier.{u, v} where
  functor := PointedCGWH.SymmetricModulePresentation.moduleOperatorEquivalence.{u, v}.functor
  inverse := PointedCGWH.SymmetricModulePresentation.moduleOperatorEquivalence.{u, v}.inverse
  unitIso := PointedCGWH.SymmetricModulePresentation.moduleOperatorEquivalence.{u, v}.unitIso
  counitIso := PointedCGWH.SymmetricModulePresentation.moduleOperatorEquivalence.{u, v}.counitIso
  functor_unitIso_comp M :=
    PointedCGWH.SymmetricModulePresentation.moduleOperatorEquivalence.{u, v}.functor_unitIso_comp M

private theorem ModuleEquivalence_eq_original : ModuleEquivalence.{u, v} =
    PointedCGWH.SymmetricModulePresentation.moduleOperatorEquivalence.{u, v} := rfl

/-- The native tensor, unit, maps and coherence are the same whole original transport. -/
private theorem nativeMonoidal_eq_transport :
    letI : MonoidalCategory
        (Mod PointedCGWH.SymmetricSequence.{u, v} PointedCGWH.sphereSequence.{u, v}) :=
      Mod.instMonoidalCategory Coefficient.{u, v}
    SymmetricSmash.monoidalCategory.{u, v} = Monoidal.transport ModuleEquivalence.{u, v} := rfl

private abbrev FreeZeroModule := NativeOmegaRecovery.NativeSymmetricFreeSource.freeModule.{u, v}
  (𝟙_ Operad.SmallFinBijGroupoid) (𝟙_ PointedCGWH.{u, v})

/-- The original whole source-unit recipe uses the actual native unit
after the complete original comparison source equality is eliminated. -/
theorem wholeSourceUnit_eq_nativeUnitComparison :
    NativeOmegaRecovery.NativeSelectedUnitTransport.Native.originalWholeSourceUnit.{u, v} =
      NativeOmegaRecovery.NativeSymmetricFreeFunction.nativeUnitComparison.{u, v} := by
  have h := NativeOmegaRecovery.NativeSelectedUnitTransport.sourceUnit_rebase
    ModuleEquivalence.{u, v}
    (NativeOmegaRecovery.NativeSymmetricFreeFunction.moduleComparisonNat
      (𝟙_ Operad.SmallFinBijGroupoid) (𝟙_ PointedCGWH.{u, v}))
    NativeOmegaRecovery.NativeSymmetricFreeFunction.zeroScalarIndexUnit.{u, v}
    NativeOmegaRecovery.NativeSelectedUnitTransport.Native.actualModuleSource_eq_originalHom.{u, v}
    (NativeOmegaRecovery.NativeSymmetricSourceMatch.nativeSource_eq_actualComparisonSource
      (𝟙_ Operad.SmallFinBijGroupoid) (𝟙_ PointedCGWH.{u, v}))
    (NativeOmegaRecovery.NativeSymmetricSourceMatch.nativeSource_eq_chosenHom
      (𝟙_ Operad.SmallFinBijGroupoid) (𝟙_ PointedCGWH.{u, v}))
  rw [NativeOmegaRecovery.NativeSymmetricFreeFunction.nativeUnitComparison_eq_wholeSourceUnit]
  exact congrArg (fun e =>
    (NativeOmegaPreparation.NativeSymmetricFunction.originalFreeComparison
      (𝟙_ Operad.SmallFinBijGroupoid) (𝟙_ PointedCGWH.{u, v})).symm ≪≫ e) h.symm

/-- The selected transport retains the original free-source isomorphism
and the same complete whole source-unit recipe. -/
theorem selectedSourceUnit_eq_wholeSourceUnit :
    NativeOmegaRecovery.NativeSelectedUnitTransport.Native.originalSelectedSourceUnit.{u, v} =
      NativeOmegaRecovery.NativeSelectedUnitTransport.Native.originalWholeSourceUnit.{u, v} := by
  unfold NativeOmegaRecovery.NativeSelectedUnitTransport.Native.originalSelectedSourceUnit
    NativeOmegaRecovery.NativeSelectedUnitTransport.Native.originalWholeSourceUnit
    NativeOmegaRecovery.NativeSelectedUnitTransport.selectedSourceUnit
    NativeOmegaRecovery.NativeSelectedUnitTransport.Native.originalFreeSourceIso
  rfl

/-- The full original selected source unit is the actual chosen native
free-function unit, with no tensor compatibility assumption. -/
theorem selectedSourceUnit_eq_nativeUnitComparison :
    NativeOmegaRecovery.NativeSelectedUnitTransport.Native.originalSelectedSourceUnit.{u, v} =
      NativeOmegaRecovery.NativeSymmetricFreeFunction.nativeUnitComparison.{u, v} :=
  selectedSourceUnit_eq_wholeSourceUnit.trans wholeSourceUnit_eq_nativeUnitComparison

/-- The unchanged transported adjunction and whole selected source unit
recover the original chosen left-unit isomorphism. -/
private theorem selectedLeftUnit_eq_original : CategoryTheory.FunctionUnitAdjunction.leftUnitIso (C :=
  HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK.Actual.SymmetricCarrier.{u, v})
      (Mod.EquivalenceFunctionTransport.adjunction Coefficient.{u, v} ModuleEquivalence.{u, v}
        (NativeOmegaRecovery.NativeSymmetricFreeSource.nativeFree.{u, v}
          (𝟙_ Operad.SmallFinBijGroupoid) (𝟙_ PointedCGWH.{u, v})))
      (NativeOmegaRecovery.NativeSelectedUnitTransport.selectedSourceUnit
        (R := PointedCGWH.SymmetricShift.functor.{u, v} (𝟙_ Operad.SmallFinBijGroupoid) ⋙
          cotensor (𝟙_ PointedCGWH.{u, v}))
        Coefficient.{u, v} ModuleEquivalence.{u, v} FreeZeroModule.{u, v}
        (NativeOmegaRecovery.NativeSymmetricFreeSource.nativeFree.{u, v}
          (𝟙_ Operad.SmallFinBijGroupoid) (𝟙_ PointedCGWH.{u, v}))
        NativeOmegaRecovery.NativeSelectedUnitTransport.Native.originalFreeSourceIso.{u, v}
        NativeOmegaRecovery.NativeSelectedUnitTransport.Native.originalModuleComparison.{u, v}
        NativeOmegaRecovery.NativeSymmetricFreeFunction.zeroScalarIndexUnit.{u, v}) =
      SymmetricSmash.freeZeroSmashUnitIso.{u, v} := by
  have hSource : NativeOmegaRecovery.NativeSelectedUnitTransport.selectedSourceUnit
      (R := PointedCGWH.SymmetricShift.functor.{u, v} (𝟙_ Operad.SmallFinBijGroupoid) ⋙
        cotensor (𝟙_ PointedCGWH.{u, v}))
      Coefficient.{u, v} ModuleEquivalence.{u, v} FreeZeroModule.{u, v}
      (NativeOmegaRecovery.NativeSymmetricFreeSource.nativeFree.{u, v}
        (𝟙_ Operad.SmallFinBijGroupoid) (𝟙_ PointedCGWH.{u, v}))
      NativeOmegaRecovery.NativeSelectedUnitTransport.Native.originalFreeSourceIso.{u, v}
      NativeOmegaRecovery.NativeSelectedUnitTransport.Native.originalModuleComparison.{u, v}
      NativeOmegaRecovery.NativeSymmetricFreeFunction.zeroScalarIndexUnit.{u, v} =
    NativeOmegaRecovery.NativeSymmetricFreeFunction.nativeUnitComparison.{u, v} := by
    change NativeOmegaRecovery.NativeSelectedUnitTransport.Native.originalSelectedSourceUnit.{u, v} = _
    exact selectedSourceUnit_eq_nativeUnitComparison
  have hAdjunction : Mod.EquivalenceFunctionTransport.adjunction Coefficient.{u, v} ModuleEquivalence.{u, v}
      (NativeOmegaRecovery.NativeSymmetricFreeSource.nativeFree.{u, v}
        (𝟙_ Operad.SmallFinBijGroupoid) (𝟙_ PointedCGWH.{u, v})) =
    NativeOmegaPreparation.NativeSymmetricFunction.adjunction
      (NativeOmegaRecovery.NativeSymmetricFreeSource.nativeFree.{u, v}
        (𝟙_ Operad.SmallFinBijGroupoid) (𝟙_ PointedCGWH.{u, v})) := rfl
  rw [hSource, hAdjunction]
  exact NativeOmegaRecovery.NativeSymmetricLambdaAdjunction.freeZeroSmashUnitIso_original.{u, v}.symm

/-- The original selected left-unit value is kept at its complete original source. -/
private def selectedLeftUnitIso :
    NativeOmegaPreparation.NativeSymmetricFunction.smashFunctor
      (NativeOmegaRecovery.NativeSymmetricFreeSource.nativeFree.{u, v}
      (𝟙_ Operad.SmallFinBijGroupoid) (𝟙_ PointedCGWH.{u, v})) ≅ 𝟭
        HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK.Actual.SymmetricCarrier.{u, v} :=
  CategoryTheory.FunctionUnitAdjunction.leftUnitIso (C :=
    HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK.Actual.SymmetricCarrier.{u, v})
      (Mod.EquivalenceFunctionTransport.adjunction Coefficient.{u, v} ModuleEquivalence.{u, v}
        (NativeOmegaRecovery.NativeSymmetricFreeSource.nativeFree.{u, v}
          (𝟙_ Operad.SmallFinBijGroupoid) (𝟙_ PointedCGWH.{u, v})))
      (NativeOmegaRecovery.NativeSelectedUnitTransport.selectedSourceUnit
        (R := PointedCGWH.SymmetricShift.functor.{u, v} (𝟙_ Operad.SmallFinBijGroupoid) ⋙
          cotensor (𝟙_ PointedCGWH.{u, v}))
        Coefficient.{u, v} ModuleEquivalence.{u, v} FreeZeroModule.{u, v}
        (NativeOmegaRecovery.NativeSymmetricFreeSource.nativeFree.{u, v}
          (𝟙_ Operad.SmallFinBijGroupoid) (𝟙_ PointedCGWH.{u, v}))
        NativeOmegaRecovery.NativeSelectedUnitTransport.Native.originalFreeSourceIso.{u, v}
        NativeOmegaRecovery.NativeSelectedUnitTransport.Native.originalModuleComparison.{u, v}
        NativeOmegaRecovery.NativeSymmetricFreeFunction.zeroScalarIndexUnit.{u, v})

/-- The full original selected unit is carried through the actual whole tensor-source equality. -/
private def selectedTensorUnitIso :
    MonoidalCategory.tensorLeft (C :=
      HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK.Actual.SymmetricCarrier.{u, v})
      (NativeOmegaRecovery.NativeSymmetricFreeSource.nativeFree.{u, v}
      (𝟙_ Operad.SmallFinBijGroupoid) (𝟙_ PointedCGWH.{u, v})) ≅ 𝟭
        HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK.Actual.SymmetricCarrier.{u, v} :=
  eqToIso (SymmetricSmash.tensorLeft_eq_originalSmash
    (NativeOmegaRecovery.NativeSymmetricFreeSource.nativeFree.{u, v}
      (𝟙_ Operad.SmallFinBijGroupoid) (𝟙_ PointedCGWH.{u, v}))) ≪≫
  CategoryTheory.FunctionUnitAdjunction.leftUnitIso (C :=
    HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK.Actual.SymmetricCarrier.{u, v})
      (Mod.EquivalenceFunctionTransport.adjunction Coefficient.{u, v} ModuleEquivalence.{u, v}
        (NativeOmegaRecovery.NativeSymmetricFreeSource.nativeFree.{u, v}
          (𝟙_ Operad.SmallFinBijGroupoid) (𝟙_ PointedCGWH.{u, v})))
      (NativeOmegaRecovery.NativeSelectedUnitTransport.selectedSourceUnit
        (R := PointedCGWH.SymmetricShift.functor.{u, v} (𝟙_ Operad.SmallFinBijGroupoid) ⋙
          cotensor (𝟙_ PointedCGWH.{u, v}))
        Coefficient.{u, v} ModuleEquivalence.{u, v} FreeZeroModule.{u, v}
        (NativeOmegaRecovery.NativeSymmetricFreeSource.nativeFree.{u, v}
          (𝟙_ Operad.SmallFinBijGroupoid) (𝟙_ PointedCGWH.{u, v}))
        NativeOmegaRecovery.NativeSelectedUnitTransport.Native.originalFreeSourceIso.{u, v}
        NativeOmegaRecovery.NativeSelectedUnitTransport.Native.originalModuleComparison.{u, v}
        NativeOmegaRecovery.NativeSymmetricFreeFunction.zeroScalarIndexUnit.{u, v})

/-- The entire original tensor/source cast and chosen left unit give the forward component. -/
private theorem selectedTensorUnitIso_hom (X :
  HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK.Actual.SymmetricCarrier.{u, v}) :
    selectedTensorUnitIso.{u, v}.hom.app X =
      (eqToIso (SymmetricSmash.tensorLeft_eq_originalSmash (NativeOmegaRecovery.NativeSymmetricFreeSource.nativeFree.{u,
        v}
      (𝟙_ Operad.SmallFinBijGroupoid) (𝟙_ PointedCGWH.{u, v})))).hom.app X ≫ selectedLeftUnitIso.{u, v}.hom.app X := rfl

/-- The actual tensor comparison retains the same entire chosen free-zero smash unit. -/
private theorem selectedTensorUnitIso_eq_original :
    selectedTensorUnitIso.{u, v} =
      eqToIso (SymmetricSmash.tensorLeft_eq_originalSmash
    (NativeOmegaRecovery.NativeSymmetricFreeSource.nativeFree.{u, v}
      (𝟙_ Operad.SmallFinBijGroupoid) (𝟙_ PointedCGWH.{u, v}))) ≪≫ SymmetricSmash.freeZeroSmashUnitIso.{u, v} := by
  unfold selectedTensorUnitIso
  exact congrArg (fun i => eqToIso (SymmetricSmash.tensorLeft_eq_originalSmash
    (NativeOmegaRecovery.NativeSymmetricFreeSource.nativeFree.{u, v}
      (𝟙_ Operad.SmallFinBijGroupoid) (𝟙_ PointedCGWH.{u, v}))) ≪≫ i) selectedLeftUnit_eq_original.{u, v}

/-- The full selected sphere-unit arrow retains its original inverse right unitor
and the complete original tensor-source cast before the selected unit component. -/
theorem freeZeroIsoSphereUnit_hom_source :
    SymmetricSmash.freeZeroIsoSphereUnit.{u, v}.hom =
      (ρ_ (Free.object (PointedCGWH.symmetricOperatorObj.{u, v}
        (𝟙_ Operad.SmallFinBijGroupoid)) (𝟙_ PointedCGWH.{u, v}))).inv ≫
        (eqToIso (SymmetricSmash.tensorLeft_eq_originalSmash
          (Free.object (PointedCGWH.symmetricOperatorObj.{u, v}
            (𝟙_ Operad.SmallFinBijGroupoid)) (𝟙_ PointedCGWH.{u, v}))) ≪≫
          SymmetricSmash.freeZeroSmashUnitIso.{u, v}).hom.app (𝟙_
            HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK.Actual.SymmetricCarrier.{u, v}) := by
  exact tensorUnitPresentation_hom (C :=
    HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK.Actual.SymmetricCarrier.{u, v})
      (Free.object (PointedCGWH.symmetricOperatorObj.{u, v}
      (𝟙_ Operad.SmallFinBijGroupoid)) (𝟙_ PointedCGWH.{u, v}))
      (NativeOmegaPreparation.NativeSymmetricFunction.smashFunctor (Free.object (PointedCGWH.symmetricOperatorObj.{u, v}
      (𝟙_ Operad.SmallFinBijGroupoid)) (𝟙_ PointedCGWH.{u, v})))
      (SymmetricSmash.tensorLeft_eq_originalSmash (Free.object (PointedCGWH.symmetricOperatorObj.{u, v}
      (𝟙_ Operad.SmallFinBijGroupoid)) (𝟙_ PointedCGWH.{u, v})))
      (SymmetricSmash.tensorObj_eq_originalSmash (Free.object (PointedCGWH.symmetricOperatorObj.{u, v}
      (𝟙_ Operad.SmallFinBijGroupoid)) (𝟙_ PointedCGWH.{u, v})) (𝟙_
        HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK.Actual.SymmetricCarrier.{u, v}))
      SymmetricSmash.freeZeroSmashUnitIso.{u, v}

/-- Every whole original module keeps the genuine source-unit mate equation. -/
private theorem nativeSelectedUnitMate : ∀ N : NativeOmegaRecovery.NativeSymmetricFreeFunction.OriginalModule.{u, v},
      (NativeOmegaRecovery.SelectedUnitTensorCompatibility.contractionCurrySource
        Coefficient.{u, v} FreeZeroModule.{u, v}
        NativeOmegaRecovery.NativeSymmetricSourceGEN.actualZeroFreeContraction.{u, v}).app N ≫
          NativeOmegaRecovery.NativeSelectedUnitTransport.Native.originalModuleComparison.hom.app N =
        ModuleEquivalence.{u, v}.unitIso.hom.app N ≫
          ModuleEquivalence.{u, v}.inverse.map
            (NativeOmegaRecovery.NativeSymmetricFreeFunction.zeroScalarIndexUnit.inv.app
              (ModuleEquivalence.{u, v}.functor.obj N)) := by
  intro N
  exact NatTrans.congr_app
    NativeOmegaRecovery.NativeSelectedUnitTransport.Native.originalModuleMate_eq_originalCarrierUnitMate.{u, v} N

/-- The original transported comparison retains the entire source-functor equality. -/
private def nativeSourceTensorComparison :
    MonoidalCategory.tensorLeft (C :=
      HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK.Actual.SymmetricCarrier.{u, v})
      (NativeOmegaRecovery.NativeSymmetricFreeSource.nativeFree.{u, v}
      (𝟙_ Operad.SmallFinBijGroupoid) (𝟙_ PointedCGWH.{u, v})) ≅ Mod.EquivalenceFunctionTransport.smashFunctor
        Coefficient.{u, v} ModuleEquivalence.{u, v} (NativeOmegaRecovery.NativeSymmetricFreeSource.nativeFree.{u, v}
      (𝟙_ Operad.SmallFinBijGroupoid) (𝟙_ PointedCGWH.{u, v})) :=
  eqToIso (tensorLeft_eq_source_ofMonoidalEquality
      (C := PointedCGWH.SymmetricSequence.{u, v}) (D :=
        HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK.Actual.SymmetricCarrier.{u, v})
      Coefficient.{u, v} ModuleEquivalence.{u, v}
      SymmetricSmash.monoidalCategory.{u, v} nativeMonoidal_eq_transport.{u, v}
        (NativeOmegaRecovery.NativeSymmetricFreeSource.nativeFree.{u, v}
      (𝟙_ Operad.SmallFinBijGroupoid) (𝟙_ PointedCGWH.{u, v})))

/-- The selected left unit retains its exact original source functor before transport. -/
private def nativeSourceLeftUnitIso : Mod.EquivalenceFunctionTransport.smashFunctor Coefficient.{u, v}
  ModuleEquivalence.{u, v} (NativeOmegaRecovery.NativeSymmetricFreeSource.nativeFree.{u, v}
      (𝟙_ Operad.SmallFinBijGroupoid) (𝟙_ PointedCGWH.{u, v})) ≅ 𝟭
        HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK.Actual.SymmetricCarrier.{u, v} :=
  CategoryTheory.FunctionUnitAdjunction.leftUnitIso (C :=
    HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK.Actual.SymmetricCarrier.{u, v})
      (Mod.EquivalenceFunctionTransport.adjunction Coefficient.{u, v} ModuleEquivalence.{u, v}
        (NativeOmegaRecovery.NativeSymmetricFreeSource.nativeFree.{u, v}
          (𝟙_ Operad.SmallFinBijGroupoid) (𝟙_ PointedCGWH.{u, v})))
      (NativeOmegaRecovery.NativeSelectedUnitTransport.selectedSourceUnit
        (R := PointedCGWH.SymmetricShift.functor.{u, v} (𝟙_ Operad.SmallFinBijGroupoid) ⋙
          cotensor (𝟙_ PointedCGWH.{u, v}))
        Coefficient.{u, v} ModuleEquivalence.{u, v} FreeZeroModule.{u, v}
        (NativeOmegaRecovery.NativeSymmetricFreeSource.nativeFree.{u, v}
          (𝟙_ Operad.SmallFinBijGroupoid) (𝟙_ PointedCGWH.{u, v}))
        NativeOmegaRecovery.NativeSelectedUnitTransport.Native.originalFreeSourceIso.{u, v}
        NativeOmegaRecovery.NativeSelectedUnitTransport.Native.originalModuleComparison.{u, v}
        NativeOmegaRecovery.NativeSymmetricFreeFunction.zeroScalarIndexUnit.{u, v})

/-- Both whole original source comparisons form the native tensor-unit value. -/
private def nativeSourceUnitIso :
    MonoidalCategory.tensorLeft (C :=
      HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK.Actual.SymmetricCarrier.{u, v})
      (NativeOmegaRecovery.NativeSymmetricFreeSource.nativeFree.{u, v}
      (𝟙_ Operad.SmallFinBijGroupoid) (𝟙_ PointedCGWH.{u, v})) ≅ 𝟭
        HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK.Actual.SymmetricCarrier.{u, v} :=
  sourceUnitIsoFactory
    (C := PointedCGWH.SymmetricSequence.{u, v}) (D :=
      HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK.Actual.SymmetricCarrier.{u, v})
    (R := PointedCGWH.SymmetricShift.functor.{u, v} (𝟙_ Operad.SmallFinBijGroupoid) ⋙
      cotensor (𝟙_ PointedCGWH.{u, v}))
    Coefficient.{u, v} ModuleEquivalence.{u, v}
    SymmetricSmash.monoidalCategory.{u, v} nativeMonoidal_eq_transport.{u, v} FreeZeroModule.{u, v}
    (NativeOmegaRecovery.NativeSymmetricFreeSource.nativeFree.{u, v}
      (𝟙_ Operad.SmallFinBijGroupoid) (𝟙_ PointedCGWH.{u, v}))
    NativeOmegaRecovery.NativeSelectedUnitTransport.Native.originalFreeSourceIso.{u, v}
    NativeOmegaRecovery.NativeSelectedUnitTransport.Native.originalModuleComparison.{u, v}
    NativeOmegaRecovery.NativeSymmetricFreeFunction.zeroScalarIndexUnit.{u, v}

/-- The entire transported source functor is the unchanged original native smash functor. -/
private theorem nativeSourceSmashFunctor_eq_original :
    Mod.EquivalenceFunctionTransport.smashFunctor Coefficient.{u, v} ModuleEquivalence.{u, v}
      (NativeOmegaRecovery.NativeSymmetricFreeSource.nativeFree.{u, v}
      (𝟙_ Operad.SmallFinBijGroupoid) (𝟙_ PointedCGWH.{u, v})) =
        NativeOmegaPreparation.NativeSymmetricFunction.smashFunctor
        (NativeOmegaRecovery.NativeSymmetricFreeSource.nativeFree.{u, v}
      (𝟙_ Operad.SmallFinBijGroupoid) (𝟙_ PointedCGWH.{u, v})) := rfl

/-- The complete equality comparison is retained under the original whole source equality. -/
private theorem nativeSourceTensorComparison_heq_original :
    HEq nativeSourceTensorComparison.{u, v} (eqToIso (SymmetricSmash.tensorLeft_eq_originalSmash
      (NativeOmegaRecovery.NativeSymmetricFreeSource.nativeFree.{u, v}
      (𝟙_ Operad.SmallFinBijGroupoid) (𝟙_ PointedCGWH.{u, v})))) :=
  eqToIso_heq_of_target_eq nativeSourceSmashFunctor_eq_original.{u, v}
    (tensorLeft_eq_source_ofMonoidalEquality
      (C := PointedCGWH.SymmetricSequence.{u, v}) (D :=
        HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK.Actual.SymmetricCarrier.{u, v})
      Coefficient.{u, v} ModuleEquivalence.{u, v}
      SymmetricSmash.monoidalCategory.{u, v} nativeMonoidal_eq_transport.{u, v}
        (NativeOmegaRecovery.NativeSymmetricFreeSource.nativeFree.{u, v}
      (𝟙_ Operad.SmallFinBijGroupoid) (𝟙_ PointedCGWH.{u, v}))) (SymmetricSmash.tensorLeft_eq_originalSmash
        (NativeOmegaRecovery.NativeSymmetricFreeSource.nativeFree.{u, v}
      (𝟙_ Operad.SmallFinBijGroupoid) (𝟙_ PointedCGWH.{u, v})))

/-- The entire selected source-unit value is retained before its native source is read. -/
private theorem nativeSourceLeftUnitIso_heq_original :
    HEq nativeSourceLeftUnitIso.{u, v} selectedLeftUnitIso.{u, v} := HEq.rfl

/-- The original intermediate source and both entire map values are eliminated
before identifying the selected native tensor unit. -/
private theorem nativeSourceUnitIso_eq_selected :
    nativeSourceUnitIso.{u, v} = selectedTensorUnitIso.{u, v} := by
  exact isoTrans_eq_of_middle_heq nativeSourceSmashFunctor_eq_original.{u, v}
    nativeSourceTensorComparison.{u, v} (eqToIso (SymmetricSmash.tensorLeft_eq_originalSmash
      (NativeOmegaRecovery.NativeSymmetricFreeSource.nativeFree.{u, v}
      (𝟙_ Operad.SmallFinBijGroupoid) (𝟙_ PointedCGWH.{u, v}))))
    nativeSourceTensorComparison_heq_original.{u, v}
    nativeSourceLeftUnitIso.{u, v} selectedLeftUnitIso.{u, v}
    nativeSourceLeftUnitIso_heq_original.{u, v}

/-- The genuine whole native module mate gives the selected tensor-unit action
before identifying its chosen sphere-unit component. -/
private theorem nativeSelectedTensorAction (X :
  HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK.Actual.SymmetricCarrier.{u, v}) :
    type_of% (
  selectedUnitActionWithMonoidalEquality
    (C := PointedCGWH.SymmetricSequence.{u, v}) (D :=
      HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK.Actual.SymmetricCarrier.{u, v})
    (R := PointedCGWH.SymmetricShift.functor.{u, v} (𝟙_ Operad.SmallFinBijGroupoid) ⋙
      cotensor (𝟙_ PointedCGWH.{u, v}))
    Coefficient.{u, v} ModuleEquivalence.{u, v}
    SymmetricSmash.monoidalCategory.{u, v} nativeMonoidal_eq_transport.{u, v} FreeZeroModule.{u, v}
    (NativeOmegaRecovery.NativeSymmetricFreeSource.nativeFree.{u, v}
    (𝟙_ Operad.SmallFinBijGroupoid) (𝟙_ PointedCGWH.{u, v}))
    NativeOmegaRecovery.NativeSelectedUnitTransport.Native.originalFreeSourceIso.{u, v}
    NativeOmegaRecovery.NativeSymmetricSourceGEN.actualZeroFreeContraction.{u, v}
    NativeOmegaRecovery.NativeSelectedUnitTransport.Native.originalModuleComparison.{u, v}
    NativeOmegaRecovery.NativeSymmetricFreeFunction.zeroScalarIndexUnit.{u, v} nativeSelectedUnitMate.{u, v} X
    ) :=
  selectedUnitActionWithMonoidalEquality
    (C := PointedCGWH.SymmetricSequence.{u, v}) (D :=
      HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK.Actual.SymmetricCarrier.{u, v})
    (R := PointedCGWH.SymmetricShift.functor.{u, v} (𝟙_ Operad.SmallFinBijGroupoid) ⋙
      cotensor (𝟙_ PointedCGWH.{u, v}))
    Coefficient.{u, v} ModuleEquivalence.{u, v}
    SymmetricSmash.monoidalCategory.{u, v} nativeMonoidal_eq_transport.{u, v} FreeZeroModule.{u, v}
    (NativeOmegaRecovery.NativeSymmetricFreeSource.nativeFree.{u, v}
    (𝟙_ Operad.SmallFinBijGroupoid) (𝟙_ PointedCGWH.{u, v}))
    NativeOmegaRecovery.NativeSelectedUnitTransport.Native.originalFreeSourceIso.{u, v}
    NativeOmegaRecovery.NativeSymmetricSourceGEN.actualZeroFreeContraction.{u, v}
    NativeOmegaRecovery.NativeSelectedUnitTransport.Native.originalModuleComparison.{u, v}
    NativeOmegaRecovery.NativeSymmetricFreeFunction.zeroScalarIndexUnit.{u, v} nativeSelectedUnitMate.{u, v} X

/-- The genuine original module mate gives the entire source tensor-unit action. -/
private theorem nativeSourceUnitIso_action (X :
  HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK.Actual.SymmetricCarrier.{u, v}) :
    nativeSourceUnitIso.{u, v}.hom.app X =
      ((((ρ_ (NativeOmegaRecovery.NativeSymmetricFreeSource.nativeFree.{u, v}
      (𝟙_ Operad.SmallFinBijGroupoid) (𝟙_ PointedCGWH.{u, v}))).inv ≫ nativeSourceUnitIso.{u, v}.hom.app (𝟙_
        HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK.Actual.SymmetricCarrier.{u, v})) ▷ X) ≫
        (λ_ X).hom) := by
  exact sourceUnitIsoFactory_action
    (C := PointedCGWH.SymmetricSequence.{u, v}) (D :=
      HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK.Actual.SymmetricCarrier.{u, v})
    (R := PointedCGWH.SymmetricShift.functor.{u, v} (𝟙_ Operad.SmallFinBijGroupoid) ⋙
      cotensor (𝟙_ PointedCGWH.{u, v}))
    Coefficient.{u, v} ModuleEquivalence.{u, v}
    SymmetricSmash.monoidalCategory.{u, v} nativeMonoidal_eq_transport.{u, v} FreeZeroModule.{u, v}
    (NativeOmegaRecovery.NativeSymmetricFreeSource.nativeFree.{u, v}
      (𝟙_ Operad.SmallFinBijGroupoid) (𝟙_ PointedCGWH.{u, v}))
    NativeOmegaRecovery.NativeSelectedUnitTransport.Native.originalFreeSourceIso.{u, v}
    NativeOmegaRecovery.NativeSymmetricSourceGEN.actualZeroFreeContraction.{u, v}
    NativeOmegaRecovery.NativeSelectedUnitTransport.Native.originalModuleComparison.{u, v}
    NativeOmegaRecovery.NativeSymmetricFreeFunction.zeroScalarIndexUnit.{u, v} nativeSelectedUnitMate.{u, v} X

/-- The genuine original module mate identifies the chosen free-zero
smash unit with the actual tensor action of its selected unit map. -/
theorem freeZeroSmashUnitIso_hom_action (X :
  HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK.Actual.SymmetricCarrier.{u, v}) :
    (eqToIso (SymmetricSmash.tensorLeft_eq_originalSmash
    (NativeOmegaRecovery.NativeSymmetricFreeSource.nativeFree.{u, v}
      (𝟙_ Operad.SmallFinBijGroupoid) (𝟙_ PointedCGWH.{u, v}))) ≪≫ SymmetricSmash.freeZeroSmashUnitIso.{u, v}).hom.app X
        =
      (SymmetricSmash.freeZeroIsoSphereUnit.{u, v}.hom ▷ X) ≫ (λ_ X).hom := by
  have hRaw := nativeSourceUnitIso_action.{u, v} X
  have hRawX := congrArg (fun i => i.hom.app X) nativeSourceUnitIso_eq_selected.{u, v}
  have hRawUnit := congrArg (fun i => i.hom.app (𝟙_
    HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK.Actual.SymmetricCarrier.{u, v}))
    nativeSourceUnitIso_eq_selected.{u, v}
  have hRawRight := congrArg (fun f => (((ρ_ (NativeOmegaRecovery.NativeSymmetricFreeSource.nativeFree.{u, v}
      (𝟙_ Operad.SmallFinBijGroupoid) (𝟙_ PointedCGWH.{u, v}))).inv ≫ f) ▷ X) ≫
    (λ_ X).hom) hRawUnit
  have hAction := hRawX.symm.trans (hRaw.trans hRawRight)
  have hX := congrArg (fun i => i.hom.app X) selectedTensorUnitIso_eq_original.{u, v}
  have hUnit := congrArg (fun i => i.hom.app (𝟙_
    HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK.Actual.SymmetricCarrier.{u, v}))
    selectedTensorUnitIso_eq_original.{u, v}
  have hRight := congrArg (fun f => (((ρ_ (NativeOmegaRecovery.NativeSymmetricFreeSource.nativeFree.{u, v}
      (𝟙_ Operad.SmallFinBijGroupoid) (𝟙_ PointedCGWH.{u, v}))).inv ≫ f) ▷ X) ≫
    (λ_ X).hom) hUnit
  exact hX.symm.trans (hAction.trans (hRight.trans
    (congrArg (fun f => (f ▷ X) ≫ (λ_ X).hom) freeZeroIsoSphereUnit_hom_source.symm)))

/-- The actual scalar free-zero source carries the original selected sphere
unit arrow through its whole source-object equality. -/
def unitMap : zeroFree.{u, v} (𝟙_ PointedCGWH.{u, v}) ⟶ (𝟙_ Carrier.{u, v}) :=
  (eqToIso (show zeroFree.{u, v} (𝟙_ PointedCGWH.{u, v}) =
    NativeOmegaRecovery.NativeSymmetricFreeSource.nativeFree.{u, v}
      (𝟙_ Operad.SmallFinBijGroupoid) (𝟙_ PointedCGWH.{u, v}) from rfl)).hom ≫
        SymmetricSmash.freeZeroIsoSphereUnit.{u, v}.hom

/-- The scalar source-object equality preserves the entire original selected unit arrow. -/
private theorem unitMap_eq_original : unitMap.{u, v} = SymmetricSmash.freeZeroIsoSphereUnit.{u, v}.hom := by
  unfold unitMap
  change (𝟙 (zeroFree.{u, v} (𝟙_ PointedCGWH.{u, v}))) ≫
    SymmetricSmash.freeZeroIsoSphereUnit.{u, v}.hom = SymmetricSmash.freeZeroIsoSphereUnit.{u, v}.hom
  exact Category.id_comp _

/-- The actual scalar unit has the original selected unit tensor action,
including its complete original source equality cast. -/
theorem unitIso_hom_action (X : Carrier.{u, v}) :
    (unitIso X).hom = (unitMap.{u, v} ▷ X) ≫ (λ_ X).hom := by
  have hOriginal := unitIso_hom_original X
  have hAction := freeZeroSmashUnitIso_hom_action X
  have hMap := unitMap_eq_original.{u, v}
  exact hOriginal.trans (hAction.trans
    (congrArg (fun f => (f ▷ X) ≫ (λ_ X).hom) hMap.symm))

/-- The original associator carries the actual scalar-unit composite
through every arbitrary right spectrum tensor. -/
@[reassoc]
theorem unitIso_hom_tensorRight (X Y : Carrier.{u, v}) :
    (α_ (zeroFree.{u, v} (𝟙_ PointedCGWH.{u, v})) X Y).inv ≫ ((unitIso X).hom ▷ Y) =
      (unitIso (X ⊗ Y)).hom := by
  simp only [unitIso_hom_action]
  rw [comp_whiskerRight, ← Category.assoc, ← associator_inv_naturality_left,
    Category.assoc, ← leftUnitor_tensor_hom]

/-- The original scalar-smash comparison at the pointed unit keeps the
entire scalar left-unit map on both arbitrary spectrum inputs. -/
@[reassoc]
theorem scalarSmashIso_unit (X Y : Carrier.{u, v}) :
    (scalarSmashIso (𝟙_ PointedCGWH.{u, v}) X Y).hom ≫
        ((scalarUnitIso X).hom ▷ Y) = (scalarUnitIso (X ⊗ Y)).hom := by
  exact interchangeUnit (zeroFree.{u, v} (𝟙_ PointedCGWH.{u, v}))
    (EnrichedFunctorCat.tensorLeft (A := PointedCGWH.SymmetricOperatorIndex.{u, v})
      (𝟙_ PointedCGWH.{u, v}))
    (tensorScalarIso.{u, v} (𝟙_ PointedCGWH.{u, v})) X Y
    (scalarUnitIso X).hom (scalarUnitIso (X ⊗ Y)).hom (unitIso_hom_tensorRight X Y)

end PointedCGWH.Spectra.NativeStableMonoidal.SymmetricScalarSmash.UnitCoherence
