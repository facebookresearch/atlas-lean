/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.Spectra.Symmetric.PointedCGWH.FunctionSpectrum.SelectedUnitTensorCompatibility
import MathlibExt.AlgebraicTopology.Spectra.Symmetric.PointedCGWH.FunctionSpectrum.LambdaAdjunction

/-!
# Original selected symmetric unit transport

The original balanced contraction, complete free source and native module
comparison are retained before any native component is selected. The generic
transport theorem identifies the selected tensor action from the genuine
module-mate equation. The native data readbacks retain the entire canonical
contraction, complete source equalities and both original carrier unit maps.
-/

set_option autoImplicit false
noncomputable section
universe uC vC
open CategoryTheory MonoidalCategory Limits
open scoped MonoidalClosed CategoryTheory.MonObj ExternalProduct

namespace NativeOmegaRecovery.NativeSelectedUnitTransport
open SelectedUnitTensorCompatibility
universe uD vD

/-- Naturality along the actual carrier counit recovers a whole arrow from
its complete original module images. -/
theorem inverse_unit_image_descent
    {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
    (E : C ≌ D) (F : C ⥤ C) (w : E.inverse ⋙ F ⋙ E.functor ≅ 𝟭 D)
    (τ : 𝟭 C ⟶ F)
    (h : ∀ N : C, w.inv.app (E.functor.obj N) =
      E.counitIso.inv.app (E.functor.obj N) ≫
        E.functor.map (τ.app (E.inverse.obj (E.functor.obj N)))) (X : D) :
    w.inv.app X = E.counitIso.inv.app X ≫ E.functor.map (τ.app (E.inverse.obj X)) := by
  let N := E.inverse.obj X
  let Y := E.functor.obj N
  let p : Y ⟶ X := E.counitIso.hom.app X
  let q : E.inverse.obj Y ⟶ N := E.inverse.map p
  have hw := w.inv.naturality p
  have hτ := τ.naturality q
  have hc := E.counitIso.inv.naturality p
  change p ≫ w.inv.app X = w.inv.app Y ≫ E.functor.map (F.map q) at hw
  change q ≫ τ.app N = τ.app (E.inverse.obj Y) ≫ F.map q at hτ
  change p ≫ E.counitIso.inv.app X =
    E.counitIso.inv.app Y ≫ E.functor.map q at hc
  apply (cancel_epi p).mp
  rw [hw, h N]
  rw [Category.assoc, ← E.functor.map_comp, ← hτ, E.functor.map_comp, ← Category.assoc, ← hc]
  exact Category.assoc p (E.counitIso.inv.app X) (E.functor.map (τ.app N))

/-- The genuine original module-mate equation determines the complete inverse
of the original function unit on every actual carrier object. -/
theorem function_unit_inv_of_module_mate_all
    {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
    (E : C ≌ D) {F : C ⥤ C} {R : D ⥤ D}
    (e : F ≅ E.functor ⋙ R ⋙ E.inverse) (u : R ≅ 𝟭 D)
    (τ : 𝟭 C ⟶ F)
    (h : ∀ N : C, τ.app N ≫ e.hom.app N =
      E.unitIso.hom.app N ≫ E.inverse.map (u.inv.app (E.functor.obj N))) (X : D) :
    (OriginalCarrierZeroSourceUnit.functionUnitIso E e u).inv.app X =
      E.counitIso.inv.app X ≫ E.functor.map (τ.app (E.inverse.obj X)) :=
  inverse_unit_image_descent E F (OriginalCarrierZeroSourceUnit.functionUnitIso E e u) τ
    (function_unit_inv_of_module_mate E e u τ h) X

variable {C : Type uC} [Category.{vC} C] [MonoidalCategory C]
  [BraidedCategory C] [MonoidalClosed C] [HasCoequalizers C] [HasEqualizers C]
  (A : CommMon C) {D : Type uD} [Category.{vD} D] (E : Mod C A.X ≌ D)

/-- The module tensor structure for the given commutative coefficient. -/
local instance nativeTransportModuleMonoidal : MonoidalCategory (Mod C A.X) :=
  Mod.instMonoidalCategory A
/-- The module internal Hom structure for the given commutative coefficient. -/
local instance nativeTransportModuleClosed : MonoidalClosed (Mod C A.X) :=
  Mod.instMonoidalClosed A

/-- The source unit retains the actual free-source comparison, whole source
equality cast, whole module comparison and both carrier functors. -/
def selectedSourceUnit (M : Mod C A.X) (S : D) (eS : M ≅ E.inverse.obj S)
    {R : D ⥤ D} (e : Mod.internalHom A M ≅ E.functor ⋙ R ⋙ E.inverse)
    (u : R ≅ 𝟭 D) : Mod.EquivalenceFunctionTransport.functor A E S ≅ 𝟭 D :=
  (Mod.EquivalenceFunctionTransport.sourceComparison A E M S eS).symm ≪≫
    OriginalCarrierZeroSourceUnit.sourceUnitFromModule E e u
      (eqToIso (Mod.EquivalenceFunctionTransport.sourceFunctor_obj A E M))

/-- The complete genuine source-mate equation recovers the selected inverse
before projecting any output coordinate. -/
theorem selectedSourceUnit_inv_of_module_mate
    (M : Mod C A.X) (S : D) (eS : M ≅ E.inverse.obj S) (t : M ⟶ Mod.regular A.X)
    {R : D ⥤ D} (e : Mod.internalHom A M ≅ E.functor ⋙ R ⋙ E.inverse)
    (u : R ≅ 𝟭 D)
    (h : ∀ N : Mod C A.X,
      (contractionCurrySource A M t).app N ≫ e.hom.app N =
        E.unitIso.hom.app N ≫ E.inverse.map (u.inv.app (E.functor.obj N))) (X : D) :
    (selectedSourceUnit A E M S eS e u).inv.app X =
      E.counitIso.inv.app X ≫ E.functor.map
        ((contractionCurrySource A M t).app (E.inverse.obj X) ≫
          (MonoidalClosed.pre eS.inv).app (E.inverse.obj X)) := by
  have hf := function_unit_inv_of_module_mate_all E e u (contractionCurrySource A M t) h X
  change ((OriginalCarrierZeroSourceUnit.functionUnitIso E e u).inv.app X ≫ 𝟙 _) ≫
      (Mod.EquivalenceFunctionTransport.sourceComparison A E M S eS).hom.app X = _
  rw [Category.comp_id, hf, original_sourceComparison_hom]
  exact (Category.assoc (E.counitIso.inv.app X)
    (E.functor.map ((contractionCurrySource A M t).app (E.inverse.obj X)))
    (E.functor.map ((MonoidalClosed.pre eS.inv).app (E.inverse.obj X)))).trans
      (congrArg (fun f => E.counitIso.inv.app X ≫ f)
        (E.functor.map_comp ((contractionCurrySource A M t).app (E.inverse.obj X))
          ((MonoidalClosed.pre eS.inv).app (E.inverse.obj X))).symm)

/-- The original balanced source adjunction carries the actual contraction
through its genuine full free-source isomorphism. -/
theorem contractionCurrySource_pre
    (M : Mod C A.X) (S : D) (eS : M ≅ E.inverse.obj S) (t : M ⟶ Mod.regular A.X)
    (N : Mod C A.X) :
    (Mod.relativeTensorInternalHomAdjunction A (E.inverse.obj S)).homEquiv N N
      (Mod.relativeTensorMap A (eS.inv ≫ t) (𝟙 N) ≫ (λ_ N).hom) =
      (contractionCurrySource A M t).app N ≫ (MonoidalClosed.pre eS.inv).app N := by
  let t₀ : M ⟶ (𝟙_ (Mod C A.X)) := t
  have hTensor : (eS.inv ≫ t₀) ⊗ₘ 𝟙 N = (eS.inv ⊗ₘ 𝟙 N) ≫ (t₀ ⊗ₘ 𝟙 N) := by
    simp only [tensorHom_id, comp_whiskerRight]
  have hq : Mod.relativeTensorMap A (eS.inv ≫ t) (𝟙 N) ≫ (λ_ N).hom =
      Mod.relativeTensorMap A eS.inv (𝟙 N) ≫ (contractionActionSource A M t).app N := by
    change ((eS.inv ≫ t₀) ⊗ₘ 𝟙 N) ≫ (λ_ N).hom =
      (eS.inv ⊗ₘ 𝟙 N) ≫ ((t₀ ⊗ₘ 𝟙 N) ≫ (λ_ N).hom)
    exact (congrArg (fun f => f ≫ (λ_ N).hom) hTensor).trans
      (Category.assoc (eS.inv ⊗ₘ 𝟙 N) (t₀ ⊗ₘ 𝟙 N) (λ_ N).hom)
  exact (congrArg ((Mod.relativeTensorInternalHomAdjunction A (E.inverse.obj S)).homEquiv N N)
    hq).trans (module_curry_pre A eS.inv N N ((contractionActionSource A M t).app N))

/-- A genuine source-mate equation gives tensor compatibility for exactly
the left-unit constructor selected by the original full function unit. -/
theorem selectedSourceUnit_action
    (M : Mod C A.X) (S : D) (eS : M ≅ E.inverse.obj S) (t : M ⟶ Mod.regular A.X)
    {R : D ⥤ D} (e : Mod.internalHom A M ≅ E.functor ⋙ R ⋙ E.inverse)
    (u : R ≅ 𝟭 D)
    (h : ∀ N : Mod C A.X,
      (contractionCurrySource A M t).app N ≫ e.hom.app N =
        E.unitIso.hom.app N ≫ E.inverse.map (u.inv.app (E.functor.obj N))) (X : D) :
    let _ : MonoidalCategory D := Monoidal.transport E
    (FunctionUnitAdjunction.leftUnitIso (Mod.EquivalenceFunctionTransport.adjunction A E S)
      (selectedSourceUnit A E M S eS e u)).hom.app X =
      ((E.counitIso.inv.app S ≫ E.functor.map (eS.inv ≫ t)) ▷ X) ≫ (λ_ X).hom := by
  let _ : MonoidalCategory D := Monoidal.transport E
  let N := E.inverse.obj X
  let q : ((Mod.relativeTensor A).obj (E.inverse.obj S)).obj N ⟶ N :=
    Mod.relativeTensorMap A (eS.inv ≫ t) (𝟙 N) ≫ (λ_ N).hom
  let adj := Mod.EquivalenceFunctionTransport.adjunction A E S
  let w := selectedSourceUnit A E M S eS e u
  let l := FunctionUnitAdjunction.leftUnitIso adj w
  have hq := contractionCurrySource_pre A E M S eS t N
  have hAdj := original_adjunction_homEquiv_image A E S X X q
  have hInv := selectedSourceUnit_inv_of_module_mate A E M S eS t e u h X
  have hCandidate : adj.homEquiv X X (E.functor.map q ≫ E.counitIso.hom.app X) = w.inv.app X :=
    hAdj.trans ((congrArg (fun f => E.counitIso.inv.app X ≫ E.functor.map f) hq).trans hInv.symm)
  have hSelected : adj.homEquiv X X (l.hom.app X) = w.inv.app X :=
    FunctionUnitAdjunction.unitInverse_adjoint adj w X
  have hArrow : l.hom.app X = E.functor.map q ≫ E.counitIso.hom.app X :=
    (adj.homEquiv X X).injective (hSelected.trans hCandidate.symm)
  have hAction := transported_unit_action E S X (eS.inv ≫ t)
  have hqArrow : q = ((eS.inv ≫ t) ▷ N) ≫ (λ_ N).hom := by
    change ((eS.inv ≫ t) ⊗ₘ 𝟙 N) ≫ (λ_ N).hom = _
    rw [tensorHom_id]
  exact hArrow.trans ((congrArg (fun f => E.functor.map f ≫ E.counitIso.hom.app X)
    hqArrow).trans hAction.symm)

/-- The same selected component at the actual unit recovers the entire
selected-unit tensor action on every original carrier object. -/
theorem selectedSourceUnit_selected_action
    (M : Mod C A.X) (S : D) (eS : M ≅ E.inverse.obj S) (t : M ⟶ Mod.regular A.X)
    {R : D ⥤ D} (e : Mod.internalHom A M ≅ E.functor ⋙ R ⋙ E.inverse)
    (u : R ≅ 𝟭 D)
    (h : ∀ N : Mod C A.X,
      (contractionCurrySource A M t).app N ≫ e.hom.app N =
        E.unitIso.hom.app N ≫ E.inverse.map (u.inv.app (E.functor.obj N))) (X : D) :
    let _ : MonoidalCategory D := Monoidal.transport E
    let l := FunctionUnitAdjunction.leftUnitIso (Mod.EquivalenceFunctionTransport.adjunction A E S)
      (selectedSourceUnit A E M S eS e u)
    l.hom.app X = (((ρ_ S).inv ≫ l.hom.app (𝟙_ D)) ▷ X) ≫ (λ_ X).hom := by
  let _ : MonoidalCategory D := Monoidal.transport E
  let l := FunctionUnitAdjunction.leftUnitIso (Mod.EquivalenceFunctionTransport.adjunction A E S)
    (selectedSourceUnit A E M S eS e u)
  let t₀ : S ⟶ (𝟙_ D) := E.counitIso.inv.app S ≫ E.functor.map (eS.inv ≫ t)
  have hUnit : l.hom.app (𝟙_ D) = (t₀ ▷ (𝟙_ D)) ≫ (λ_ (𝟙_ D)).hom :=
    selectedSourceUnit_action A E M S eS t e u h (𝟙_ D)
  have hMap : (ρ_ S).inv ≫ l.hom.app (𝟙_ D) = t₀ :=
    selected_unit_map_eq S (l.hom.app (𝟙_ D)) t₀ hUnit
  have hX : l.hom.app X = (t₀ ▷ X) ≫ (λ_ X).hom :=
    selectedSourceUnit_action A E M S eS t e u h X
  exact hX.trans (congrArg (fun f => (f ▷ X) ≫ (λ_ X).hom) hMap.symm)

end NativeOmegaRecovery.NativeSelectedUnitTransport

namespace NativeOmegaRecovery.NativeSelectedUnitTransport
universe uD vD

/-- A genuine complete source-functor equality is applied to the whole
original comparison before any component is selected. -/
def rebaseComparison {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
    {F F' K : C ⥤ D} (e : F ≅ K) (h : F = F') : F' ≅ K := (eqToIso h).symm ≪≫ e

/-- Both complete source equality casts carry the same original unit after
rebasing by the actual full source-functor equality. -/
theorem sourceUnit_rebase {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
    (E : C ≌ D) {F F' : C ⥤ C} {R S : D ⥤ D}
    (e : F ≅ E.functor ⋙ R ⋙ E.inverse) (u : R ≅ 𝟭 D)
    (h : F = F') (hS : S = E.inverse ⋙ F ⋙ E.functor)
    (hS' : S = E.inverse ⋙ F' ⋙ E.functor) :
    OriginalCarrierZeroSourceUnit.sourceUnitFromModule E e u (eqToIso hS) =
      OriginalCarrierZeroSourceUnit.sourceUnitFromModule E (rebaseComparison e h) u (eqToIso hS') := by
  cases h
  have hs : hS = hS' := Subsingleton.elim _ _
  cases hs
  have he : rebaseComparison e rfl = e := by
    apply Iso.ext
    change (𝟙 _ ≫ e.hom) = e.hom
    exact Category.id_comp e.hom
  rw [he]

end NativeOmegaRecovery.NativeSelectedUnitTransport

namespace NativeOmegaRecovery.NativeSelectedUnitTransport

/-- Equality of the complete original monoid data identifies the entire
free-forgetful contraction before its source or target is projected. -/
theorem freeContraction_monObj_heq
    {C : Type uC} [Category.{vC} C] [MonoidalCategory C]
    (R : C) (m m' : MonObj R) (hm : m = m') (P : C) (u : P ⟶ (𝟙_ C)) :
    HEq (letI : MonObj R := m;
      ((Mod.freeForgetAdjunction R).homEquiv P (Mod.regular R)).symm
        (u ≫ (η : (𝟙_ C) ⟶ R)))
      (letI : MonObj R := m';
      ((Mod.freeForgetAdjunction R).homEquiv P (Mod.regular R)).symm
        (u ≫ (η : (𝟙_ C) ⟶ R))) := by
  cases hm
  rfl

/-- The same complete monoid equality also retains both endpoints and the
whole free-forgetful contraction as an original arrow record. -/
theorem freeContraction_arrow_monObj_heq
    {C : Type uC} [Category.{vC} C] [MonoidalCategory C]
    (R : C) (m m' : MonObj R) (hm : m = m') (P : C) (u : P ⟶ (𝟙_ C)) :
    HEq (letI : MonObj R := m;
      Arrow.mk (((Mod.freeForgetAdjunction R).homEquiv P (Mod.regular R)).symm
        (u ≫ (η : (𝟙_ C) ⟶ R))))
      (letI : MonObj R := m';
      Arrow.mk (((Mod.freeForgetAdjunction R).homEquiv P (Mod.regular R)).symm
        (u ≫ (η : (𝟙_ C) ⟶ R)))) := by
  cases hm
  rfl

/-- The complete given source-object and source-map equalities are eliminated
before forming the original balanced adjunct natural transformation. -/
theorem contractionCurrySource_heq_of_source_data
    {C : Type uC} [Category.{vC} C] [MonoidalCategory C]
    [BraidedCategory C] [MonoidalClosed C] [HasCoequalizers C] [HasEqualizers C]
    (A : CommMon C) (M M' : Mod C A.X)
    (t : M ⟶ Mod.regular A.X) (t' : M' ⟶ Mod.regular A.X)
    (hM : M = M') (ht : HEq t t') :
    HEq (SelectedUnitTensorCompatibility.contractionCurrySource A M t)
      (SelectedUnitTensorCompatibility.contractionCurrySource A M' t') := by
  cases hM
  cases ht
  rfl

end NativeOmegaRecovery.NativeSelectedUnitTransport

namespace NativeOmegaRecovery.NativeSelectedUnitTransport
open SelectedUnitTensorCompatibility
universe uD vD

/-- The canonical free-source action is the same complete original action
before any native coefficient or module is substituted. -/
theorem contractionCurrySource_free_eq
    {C : Type uC} [Category.{vC} C] [MonoidalCategory C]
    [BraidedCategory C] [MonoidalClosed C] [HasCoequalizers C] [HasEqualizers C]
    (A : CommMon C) (P : C) (u : P ⟶ (𝟙_ C)) :
    contractionCurrySource A ((Mod.free A.X).obj P) (freeUnitContraction A P u) =
      contractionCurry A P u := by
  apply NatTrans.ext
  funext N
  rfl

/-- Entire source-functor and adjunct equalities are eliminated before
rebasing the original whole module mate. -/
theorem mate_rebase_of_full_source_eq
    {C : Type uC} [Category.{vC} C] {F F' K : C ⥤ C}
    (hF : F = F') (τ : 𝟭 C ⟶ F) (τ' : 𝟭 C ⟶ F') (hτ : HEq τ τ') (e : F ≅ K) :
    τ ≫ e.hom = τ' ≫ (rebaseComparison e hF).hom := by
  cases hF
  cases hτ
  have he : rebaseComparison e rfl = e := by
    apply Iso.ext
    change (𝟙 _ ≫ e.hom) = e.hom
    exact Category.id_comp e.hom
  rw [he]

end NativeOmegaRecovery.NativeSelectedUnitTransport

namespace NativeOmegaRecovery.NativeSelectedUnitTransport.Native
universe u v
open CategoryTheory.EnrichedFunctorCat
open PointedCGWH.SymmetricModulePresentation
open NativeSymmetricFreeFunction NativeSymmetricFreeSource

private abbrev I := Operad.SmallFinBijGroupoid
private abbrev V := PointedCGWH.{u, v}
private abbrev A := PointedCGWH.sphereSequenceCommMon.{u, v}
private abbrev Carrier := EnrichedFunctorCat V.{u, v} PointedCGWH.SymmetricOperatorIndex.{u, v}
private abbrev Modules := NativeSymmetricFreeFunction.OriginalModule.{u, v}
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

private abbrev FreeZero := NativeSymmetricFreeSource.nativeFree.{u, v} (𝟙_ I) (𝟙_ V.{u, v})
private abbrev FreeZeroModule := NativeSymmetricFreeSource.freeModule.{u, v} (𝟙_ I) (𝟙_ V.{u, v})

/-- The entire actual original comparison source is the same whole internal
Hom out of the original Day free-zero module. -/
theorem actualModuleSource_eq_originalHom :
    NativeScalarCoefficient.originalComparisonSourceFunctor.{u, v} (𝟙_ I) (𝟙_ V.{u, v}) =
      Mod.internalHom A.{u, v} FreeZeroModule.{u, v} :=
  (NativeSymmetricSourceMatch.actualSource_eq_recipe.{u, v} (𝟙_ I) (𝟙_ V.{u, v})).trans
    (NativeSymmetricSourceMatch.chosenHomSource_eq_recipe.{u, v} (𝟙_ I) (𝟙_ V.{u, v})).symm

/-- The same entire original module comparison retains its actual complete
source equality before any original target module is selected. -/
def originalModuleComparison :=
  rebaseComparison (moduleComparisonNat.{u, v} (𝟙_ I) (𝟙_ V.{u, v}))
    actualModuleSource_eq_originalHom.{u, v}

/-- The original whole source recipe uses that same complete original
comparison and actual free-source isomorphism. -/
def originalFreeSourceIso := freeIso.{u, v} (𝟙_ I) (𝟙_ V.{u, v})

/-- The original selected zero-source unit uses the complete free-source
isomorphism, rebased module comparison, and scalar/index unit comparison. -/
def originalSelectedSourceUnit :=
  selectedSourceUnit
    (R := PointedCGWH.SymmetricShift.functor.{u, v} (𝟙_ I) ⋙ cotensor (𝟙_ V.{u, v}))
    A.{u, v} E.{u, v} FreeZeroModule.{u, v} FreeZero.{u, v}
    originalFreeSourceIso.{u, v} originalModuleComparison.{u, v}
    zeroScalarIndexUnit.{u, v}

/-- The unchanged complete native source prefix carries the rebased actual
module comparison through the actual native source equality. -/
def originalWholeSourceUnit :=
  (NativeOmegaPreparation.NativeSymmetricFunction.originalFreeComparison.{u, v}
    (𝟙_ I) (𝟙_ V.{u, v})).symm ≪≫
    OriginalCarrierZeroSourceUnit.sourceUnitFromModule
      (R := PointedCGWH.SymmetricShift.functor.{u, v} (𝟙_ I) ⋙ cotensor (𝟙_ V.{u, v})) E.{u, v}
      originalModuleComparison.{u, v} zeroScalarIndexUnit.{u, v}
      (eqToIso (NativeSymmetricSourceMatch.nativeSource_eq_chosenHom.{u, v}
        (𝟙_ I) (𝟙_ V.{u, v})))

/-- The genuine whole source-mate left side is formed before any native
module coordinate is selected. -/
def originalModuleMate :=
  NativeSymmetricSelectedUnit.originalContractionCurry.{u, v} ≫ originalModuleComparison.{u, v}.hom

/-- The same original carrier unit and scalar/index inverse give the complete
right side of the original module source equation. -/
def originalCarrierUnitMate :=
  E.{u, v}.unitIso.hom ≫ Functor.whiskerLeft E.{u, v}.functor
    (Functor.whiskerRight zeroScalarIndexUnit.{u, v}.inv E.{u, v}.inverse)

private abbrev ZeroDiagram : PointedCGWH.SymmetricSequence.{u, v} :=
  .mk ((evaluationLeftAdjoint V.{u, v} (𝟙_ I)).obj (𝟙_ V.{u, v}))
private abbrev S := PointedCGWH.sphereSequence.{u, v}

/-- The complete canonical free contraction uses the actual original Day
unit arrow and original commutative sphere monoid. -/
def canonicalZeroContraction :=
  SelectedUnitTensorCompatibility.freeUnitContraction A.{u, v} ZeroDiagram.{u, v}
    FreeFunctionSourceEvaluation.originalZeroDiagramUnit

/-- The entire original zero-free contraction is retained under the
proved equality of its complete original sphere monoid data. -/
theorem actualZeroFreeContraction_heq_canonical :
    HEq NativeSymmetricSourceGEN.actualZeroFreeContraction.{u, v}
      canonicalZeroContraction.{u, v} :=
  freeContraction_monObj_heq S.{u, v} PointedCGWH.sphereSequenceMonObj.{u, v} A.{u, v}.mon
    NativeScalarCoefficient.sphereCoefficient_mon_eq.{u, v}.symm ZeroDiagram.{u, v}
      FreeFunctionSourceEvaluation.originalZeroDiagramUnit

/-- Both complete original endpoints and the contraction map are retained
in the same genuine full arrow record under the original sphere data equality. -/
theorem actualZeroFreeContraction_arrow_heq_canonical :
    HEq (Arrow.mk NativeSymmetricSourceGEN.actualZeroFreeContraction.{u, v})
      (Arrow.mk canonicalZeroContraction.{u, v}) :=
  freeContraction_arrow_monObj_heq S.{u, v} PointedCGWH.sphereSequenceMonObj.{u, v} A.{u, v}.mon
    NativeScalarCoefficient.sphereCoefficient_mon_eq.{u, v}.symm ZeroDiagram.{u, v}
      FreeFunctionSourceEvaluation.originalZeroDiagramUnit

/-- The whole original arrow equality is obtained before its complete
original free source is read. -/
theorem actualZeroFreeContraction_arrow_eq_canonical :
    Arrow.mk NativeSymmetricSourceGEN.actualZeroFreeContraction.{u, v} =
      Arrow.mk canonicalZeroContraction.{u, v} :=
  eq_of_heq actualZeroFreeContraction_arrow_heq_canonical.{u, v}

/-- The complete original free source is the actual canonical free object,
read only after eliminating the whole original arrow equality. -/
theorem actualFreeZeroModule_eq_canonical :
    FreeZeroModule.{u, v} = (Mod.free A.{u, v}.X).obj ZeroDiagram.{u, v} :=
  congrArg Arrow.left actualZeroFreeContraction_arrow_eq_canonical.{u, v}

/-- The same original source equality identifies the whole internal-Hom
functor before selecting any target module or output coordinate. -/
theorem originalHom_eq_canonical :
    Mod.internalHom A.{u, v} FreeZeroModule.{u, v} =
      Mod.internalHom A.{u, v} ((Mod.free A.{u, v}.X).obj ZeroDiagram.{u, v}) :=
  congrArg (Mod.internalHom A.{u, v}) actualFreeZeroModule_eq_canonical.{u, v}

/-- The same canonical contraction is transposed by the original balanced
module adjunction on every entire original target module. -/
def canonicalZeroCurry :=
  SelectedUnitTensorCompatibility.contractionCurry A.{u, v} ZeroDiagram.{u, v}
    FreeFunctionSourceEvaluation.originalZeroDiagramUnit

/-- The actual whole balanced adjunct is the canonical contraction adjunct,
using only the original entire arrow and source data equalities. -/
theorem originalContractionCurry_heq_canonical :
    HEq NativeSymmetricSelectedUnit.originalContractionCurry.{u, v} canonicalZeroCurry.{u, v} := by
  have h := contractionCurrySource_heq_of_source_data A.{u, v} FreeZeroModule.{u, v}
    ((Mod.free A.{u, v}.X).obj ZeroDiagram.{u, v})
    NativeSymmetricSourceGEN.actualZeroFreeContraction.{u, v} canonicalZeroContraction.{u, v}
    actualFreeZeroModule_eq_canonical.{u, v} actualZeroFreeContraction_heq_canonical.{u, v}
  have hc : SelectedUnitTensorCompatibility.contractionCurrySource A.{u, v}
      ((Mod.free A.{u, v}.X).obj ZeroDiagram.{u, v}) canonicalZeroContraction.{u, v} =
        canonicalZeroCurry.{u, v} :=
    contractionCurrySource_free_eq A.{u, v} ZeroDiagram.{u, v}
      FreeFunctionSourceEvaluation.originalZeroDiagramUnit
  exact h.trans (heq_of_eq hc)

/-- The entire original module comparison is rebased by its genuine complete
free-source equality before any original module component is selected. -/
def canonicalModuleComparison :=
  rebaseComparison originalModuleComparison.{u, v} originalHom_eq_canonical.{u, v}

/-- Both actual original canonical sources form this whole mate before
selecting a target module or enriched output. -/
def canonicalModuleMate := canonicalZeroCurry.{u, v} ≫ canonicalModuleComparison.{u, v}.hom

/-- The whole actual mate and whole canonical mate agree through the genuine
original source and contraction data, before any coordinate is selected. -/
theorem originalModuleMate_eq_canonical :
    originalModuleMate.{u, v} = canonicalModuleMate.{u, v} :=
  mate_rebase_of_full_source_eq originalHom_eq_canonical.{u, v}
    NativeSymmetricSelectedUnit.originalContractionCurry.{u, v} canonicalZeroCurry.{u, v}
    originalContractionCurry_heq_canonical.{u, v} originalModuleComparison.{u, v}

/-- The actual original target comparison keeps its complete scalar closed
unit identity at every unchanged native output. -/
theorem targetSequenceNatIso_zero_hom_component (N : Modules.{u, v}) (n : I) :
    ((targetSequenceNatIso.{u, v} (𝟙_ I) (𝟙_ V.{u, v})).hom.app N).natTrans.app n =
      𝟙 ((ihom (𝟙_ V.{u, v})).obj (N.X.functor.obj (n ⊗ (𝟙_ I)))) :=
  targetSequenceIso_inv_component.{u, v} (𝟙_ I) (𝟙_ V.{u, v}) N n

end NativeOmegaRecovery.NativeSelectedUnitTransport.Native

namespace NativeOmegaRecovery.NativeSelectedUnitTransport.Day
universe uI vI uV vV
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

private abbrev ZeroDiagram : DayFunctor I V :=
  .mk ((evaluationLeftAdjoint V (𝟙_ I)).obj (𝟙_ V))

/-- The complete canonical free contraction gives the original scalar/index
unit pair at every original Day output, through the original balanced adjunct. -/
theorem canonical_zero_contraction_pair (N : Mod (DayFunctor I V) A.X) (n : I) :
    (((SelectedUnitTensorCompatibility.contractionCurry A ZeroDiagram
      FreeFunctionSourceEvaluation.originalZeroDiagramUnit).app N).hom ≫
        (FullFreeFunctionPair.comparison A (𝟙_ I) (𝟙_ V) N).hom).natTrans.app n =
      N.X.functor.map (ρ_ n).inv ≫
        MonoidalClosed.unitNatIso.hom.app (N.X.functor.obj (n ⊗ (𝟙_ I))) := by
  let P : DayFunctor I V := ZeroDiagram
  let u : P ⟶ (𝟙_ (DayFunctor I V)) := FreeFunctionSourceEvaluation.originalZeroDiagramUnit
  let c := (SelectedUnitTensorCompatibility.contractionCurry A P u).app N
  have hc := SelectedUnitTensorCompatibility.contractionCurry_app A P u N
  have hp : c.hom ≫ Mod.FreeInternalHom.forward A P N =
      MonoidalClosed.curry ((u ▷ N.X) ≫ (λ_ N.X).hom) :=
    (congrArg (fun f => f.hom ≫ Mod.FreeInternalHom.forward A P N) hc).trans
      (SelectedUnitTensorCompatibility.freeUnitContraction_curry_forward A P u N)
  exact SelectedUnitTensorCompatibility.Day.zero_unit_pair_of_projection A N c hp n

end NativeOmegaRecovery.NativeSelectedUnitTransport.Day
