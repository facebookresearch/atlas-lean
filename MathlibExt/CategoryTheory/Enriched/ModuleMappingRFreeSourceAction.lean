/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module
public import MathlibExt.CategoryTheory.Enriched.SphereOperatorRightShiftAction
public import MathlibExt.CategoryTheory.Enriched.FreeAdjunctionSource
public import MathlibExt.CategoryTheory.Enriched.RightModuleFreeEvaluation
public import MathlibExt.CategoryTheory.Enriched.ModuleMappingRFreeEvaluation
public import MathlibExt.CategoryTheory.Monoidal.RightModuleRegularMapping
public import MathlibExt.CategoryTheory.Enriched.SphereOperatorRightSphereNaturality
public import MathlibExt.CategoryTheory.Enriched.SphereOperatorActionReconstruction
public import MathlibExt.CategoryTheory.Enriched.ScalarCotensorUnit
public import MathlibExt.CategoryTheory.Enriched.ScalarCorners
public import MathlibExt.CategoryTheory.Enriched.Monoidal.DayConvolution.BraidingGenerators
public import MathlibExt.CategoryTheory.Enriched.Ordinary.FunctorCategory
public import MathlibExt.CategoryTheory.Enriched.ModuleMappingRSourceEvaluation

/-!
# Free-source mapping actions over enriched monoidal categories

The original free/evaluation comparison is linear for the entire inherited
right-module action. Its scalar cotensor and right-shift descriptions retain
all source coefficients, enriched Hom actions, braids, and equivalence units.
Precomposition by the actual free sphere map constructs the full source delta.
All implementations use arbitrary enriched monoidal data; spectrum specializations
only instantiate these constructions.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section
open CategoryTheory MonoidalCategory BraidedCategory Limits
open CategoryTheory.Enriched CategoryTheory.EnrichedFunctorCat
open CategoryTheory.Enriched.SphereOperator
open scoped MonoidalClosed
universe uV vV uI vI

namespace CategoryTheory.Enriched.ModuleMappingR.FreeSourceAction.Internal
variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [SymmetricCategory V] [MonoidalClosed V]
  {I : Type uI} [Category.{vI} I] [MonoidalCategory I] [SymmetricCategory I]
  [EnrichedOrdinaryCategory V I]
  (d : EnrichedMonoidalCategoryData V I) (S : EnrichedFunctor V I V)
  (L : EnrichedFunctor.LaxMonoidalData d
    (MonoidalClosed.enrichedMonoidalCategoryDataSelf V) S)
  [∀ n k : I, HasCoproduct (weightedCoend.relations (weight d n k) S)]
  [∀ n k : I, HasCoproduct (weightedCoend.objects (weight d n k) S)]
  [∀ n k : I, HasCoequalizer (weightedCoend.leftMap (weight d n k) S)
    (weightedCoend.rightMap (weight d n k) S)]

open CategoryTheory.Enriched.SphereOperator.RightShift

omit [SymmetricCategory I] in
/-- Every original coefficient action survives the complete actual right shift. -/
theorem shiftedCoefficientAction (F : EnrichedFunctorCat V (OperatorIndex d S L))
    (r n k a : I) (f : a ⊗ n ⟶ k) :
    coefficientAction d S L
      ((CategoryTheory.Enriched.SphereOperator.RightShift.shift d S L r).obj F) n k a f =
      coefficientAction d S L F (n ⊗ r) (k ⊗ r) a
        (GenericRightTensor.label r n k a f) := by
  let q := coefficientHom d S n k a f
  let t := GenericRightTensor.hom d S r n k
  let q' := coefficientHom d S (n ⊗ r) (k ⊗ r) a
    (GenericRightTensor.label r n k a f)
  let p := F.toEnrichedFunctor.map
    (⟨n ⊗ r⟩ : OperatorIndex d S L) (⟨k ⊗ r⟩ : OperatorIndex d S L)
  have hp : q ≫ (t ≫ p) = q' ≫ p :=
    (Category.assoc q t p).symm.trans
      (congrArg (fun z => z ≫ p)
        (CategoryTheory.Enriched.SphereOperator.RightShift.coefficientHom_shift d S r n k a f))
  unfold coefficientAction
  rw [← MonoidalClosed.uncurry_natural_left, ← MonoidalClosed.uncurry_natural_left]
  change MonoidalClosed.uncurry (q ≫ (t ≫ p)) = MonoidalClosed.uncurry (q' ≫ p)
  exact congrArg MonoidalClosed.uncurry hp

/-- The original right sphere action keeps the full three-block exchange. -/
theorem rightSphereAction_shift (F : EnrichedFunctorCat V (OperatorIndex d S L))
    (r c a : I) :
    rightSphereAction d S L
      ((CategoryTheory.Enriched.SphereOperator.RightShift.shift d S L r).obj F) c a =
      rightSphereAction d S L F (c ⊗ r) a ≫
        ((indexRestriction d S L).obj F).toEnrichedFunctor.toOrdinaryFunctor.map
          (CategoryTheory.Enriched.SphereOperator.RightShift.blockSwap r c a).hom := by
  rw [rightSphereAction, shiftedCoefficientAction,
    CategoryTheory.Enriched.SphereOperator.RightShift.blockSwap_label]
  exact (coefficientAction_postcompose d S L F (c ⊗ r) ((c ⊗ r) ⊗ a)
    ((c ⊗ a) ⊗ r) a (β_ a (c ⊗ r)).hom
      (CategoryTheory.Enriched.SphereOperator.RightShift.blockSwap r c a).hom).symm

/-- Original parameter braiding retains the complete associator and block exchange. -/
theorem blockSwap_parameter (r c a : I) :
    ((β_ r c).hom ▷ a) ≫ (CategoryTheory.Enriched.SphereOperator.RightShift.blockSwap r c a).hom =
      (α_ r c a).hom ≫ (β_ r (c ⊗ a)).hom := by
  rw [braiding_tensor_right_hom]
  simp only [CategoryTheory.Enriched.SphereOperator.RightShift.blockSwap, Iso.trans_hom,
    whiskerLeftIso_hom,
    Iso.symm_hom, Iso.hom_inv_id_assoc]

omit [SymmetricCategory I] in
/-- Actual double uncurry retains the whole coefficient Hom and original action. -/
theorem cotensorCoefficientAction_uncurry
    (F : EnrichedFunctorCat V (OperatorIndex d S L)) (X : V)
    (n k a : I) (f : a ⊗ n ⟶ k) :
    MonoidalClosed.uncurry (A := X)
        (coefficientAction d S L (cotensorObject X F) n k a f) =
      (α_ X ((ihom X).obj (F.toEnrichedFunctor.obj ⟨n⟩)) (S.obj a)).inv ≫
        ((ihom.ev X).app (F.toEnrichedFunctor.obj ⟨n⟩) ▷ S.obj a) ≫
          coefficientAction d S L F n k a f := by
  let H : V := (⟨n⟩ : OperatorIndex d S L) ⟶[V] ⟨k⟩
  let P := (ihom X).obj (F.toEnrichedFunctor.obj ⟨n⟩)
  let q : S.obj a ⟶ H := coefficientHom d S n k a f
  let ev : X ⊗ P ⟶ F.toEnrichedFunctor.obj ⟨n⟩ :=
    (ihom.ev X).app (F.toEnrichedFunctor.obj ⟨n⟩)
  let m := MonoidalClosed.uncurry (F.toEnrichedFunctor.map
    (⟨n⟩ : OperatorIndex d S L) ⟨k⟩)
  unfold coefficientAction
  rw [MonoidalClosed.uncurry_natural_left, EnrichedFunctor.cotensor_doubleUncurry]
  change (X ◁ (P ◁ q)) ≫ (α_ X P H).inv ≫ (ev ▷ H) ≫ m =
    (α_ X P (S.obj a)).inv ≫ (ev ▷ S.obj a) ≫
      (F.toEnrichedFunctor.obj ⟨n⟩ ◁ q) ≫ m
  calc
    _ = (α_ X P (S.obj a)).inv ≫ ((X ⊗ P) ◁ q) ≫ (ev ▷ H) ≫ m := by
      simpa only [Category.assoc] using congrArg
        (fun z => z ≫ (ev ▷ H) ≫ m) (associator_inv_naturality_right X P q)
    _ = _ := by
      simpa only [Category.assoc] using congrArg
        (fun z => (α_ X P (S.obj a)).inv ≫ z ≫ m) (whisker_exchange ev q)

/-- The original scalar cotensor right action is the actual evaluation action. -/
theorem cotensorSphereAction_uncurry
    (F : EnrichedFunctorCat V (OperatorIndex d S L)) (X : V) (c a : I) :
    MonoidalClosed.uncurry (A := X)
        (rightSphereAction d S L (cotensorObject X F) c a) =
      (α_ X ((ihom X).obj (F.toEnrichedFunctor.obj ⟨c⟩)) (S.obj a)).inv ≫
        ((ihom.ev X).app (F.toEnrichedFunctor.obj ⟨c⟩) ▷ S.obj a) ≫
          rightSphereAction d S L F c a :=
  cotensorCoefficientAction_uncurry d S L F X c (c ⊗ a) a (β_ a c).hom

/-- Every full parameter map retains the actual cotensor evaluation and sphere action. -/
theorem cotensorSphereAction_parameter_uncurry
    (F : EnrichedFunctorCat V (OperatorIndex d S L)) (X : V) (c a : I)
    {P : V} (h : P ⟶ (ihom X).obj (F.toEnrichedFunctor.obj ⟨c⟩)) :
    MonoidalClosed.uncurry (A := X)
        ((h ⊗ₘ 𝟙 (S.obj a)) ≫ rightSphereAction d S L (cotensorObject X F) c a) =
      (α_ X P (S.obj a)).inv ≫ (MonoidalClosed.uncurry h ▷ S.obj a) ≫
        rightSphereAction d S L F c a := by
  rw [tensorHom_id, MonoidalClosed.uncurry_natural_left, cotensorSphereAction_uncurry,
    associator_inv_naturality_middle_assoc, ← comp_whiskerRight_assoc,
    ← MonoidalClosed.uncurry_eq]

end CategoryTheory.Enriched.ModuleMappingR.FreeSourceAction.Internal

universe uJ uA

namespace CategoryTheory.Enriched.ModuleMappingR.FreeSourceAction.Mapping

attribute [local instance] Enriched.prodCategory
attribute [local instance] EnrichedDayKernel.ColimitMonoidal.smallestColimits
attribute [local instance] SphereModuleMappingEnd.moduleCategory
attribute [local instance] MonoidalLeftAction.monoidalOppositeLeftAction

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [SymmetricCategory V] [MonoidalClosed V]
  {I : Type uI} [Category.{vI} I] [MonoidalCategory I] [SymmetricCategory I]
  [EnrichedOrdinaryCategory V I]
  [HasColimitsOfSize.{uI, uI} V] [HasProducts.{uI} V] [HasEqualizers V]
  (d : EnrichedMonoidalCategoryData V I)
  (b : EnrichedBraidedMonoidalCategoryData V I d)
  (S : EnrichedFunctor V I V)
  (L : EnrichedFunctor.LaxMonoidalData d
    (MonoidalClosed.enrichedMonoidalCategoryDataSelf V) S)

open EnrichedDayKernel ModuleMappingR

omit [HasColimitsOfSize.{uI, uI} V] [HasProducts.{uI} V] [HasEqualizers V] in
private theorem component_eqToHom {A : Type uA} [EnrichedCategory V A]
    {F G : EnrichedFunctorCat V A} (p : F = G) (a : A) :
    component (eqToHom p) a =
      eqToHom (congrArg (fun F : EnrichedFunctorCat V A => F.toEnrichedFunctor.obj a) p) := by
  cases p
  exact component_id F a

omit [HasColimitsOfSize.{uI, uI} V] [HasProducts.{uI} V] [HasEqualizers V] in
/-- The actual complete translated target comparison retains the original block map. -/
theorem translationTargetIso_hom_component (Y : EnrichedFunctorCat V I) (r c : I) :
    component
      (CategoryTheory.Enriched.ModuleMappingR.FreeEvaluation.translationTargetIso d b Y r).hom c =
      Y.toEnrichedFunctor.toOrdinaryFunctor.map (β_ r c).hom := by
  unfold CategoryTheory.Enriched.ModuleMappingR.FreeEvaluation.translationTargetIso
  change @Eq
    (Y.toEnrichedFunctor.obj (r ⊗ c) ⟶ Y.toEnrichedFunctor.obj (c ⊗ r)) _ _
  rw [Iso.trans_hom, component_comp,
    CategoryTheory.Enriched.ModuleMappingR.FreeEvaluation.translationIso_hom_component]
  change Y.toEnrichedFunctor.toOrdinaryFunctor.map (β_ r c).hom ≫
    component (eqToHom (Closed.translatedTarget_eq_restriction d Y r).symm) c = _
  rw [component_eqToHom]
  change Y.toEnrichedFunctor.toOrdinaryFunctor.map (β_ r c).hom ≫ 𝟙 _ = _
  exact Category.comp_id _

/-- Every original source, translation and shift inverse remains in the full forward value. -/
theorem rawRightShiftDiagramIso_hom_component (r : I) (X : V) (N : Module d S L)
    (Z : EnrichedFunctorCat V I)
    (e : Z ≅ Closed.translatedTarget d (SphereModuleMappingEnd.diagram d S L N) r)
    (c : I) :
    component
      (CategoryTheory.Enriched.ModuleMappingR.FreeEvaluation.rawRightShiftDiagramIso d b S L r X N
        Z e).hom c =
      (CategoryTheory.Enriched.ModuleMappingR.FreeEvaluation.valueIso d b S L r X N c).hom ≫
        (ihom X).map
          ((SphereModuleMappingEnd.diagram d S L N).toEnrichedFunctor.toOrdinaryFunctor.map
          (β_ r c).hom) ≫ (ihom X).map (component e.inv c) := by
  unfold CategoryTheory.Enriched.ModuleMappingR.FreeEvaluation.rawRightShiftDiagramIso
  change @Eq
    (value d b S L (CategoryTheory.Enriched.ModuleMappingR.FreeEvaluation.freeAt d S L r X) N c ⟶
      (ihom X).obj (Z.toEnrichedFunctor.obj c)) _ _
  rw [Iso.trans_hom, Iso.trans_hom, component_comp, component_comp,
    CategoryTheory.Enriched.ModuleMappingR.FreeEvaluation.diagramIso_hom_component]
  change (CategoryTheory.Enriched.ModuleMappingR.FreeEvaluation.valueIso d b S L r X N c).hom ≫
    component (cotensorMap X
      (CategoryTheory.Enriched.ModuleMappingR.FreeEvaluation.translationTargetIso d b
        (SphereModuleMappingEnd.diagram d S L N) r).hom)
      c ≫ component (cotensorMap X e.inv) c = _
  rw [cotensorMap_component, cotensorMap_component, translationTargetIso_hom_component]

/-- The final genuine restriction retains the original full value and block comparison maps. -/
theorem rawRightShiftRestrictionIso_hom_component {J : Type uJ} [EnrichedCategory V J]
    (i : EnrichedFunctor V I J) (r : I) (X : V) (N : Module d S L)
    (F : EnrichedFunctorCat V J)
    (e : restrictionObject i F ≅
      Closed.translatedTarget d (SphereModuleMappingEnd.diagram d S L N) r) (c : I) :
    component
      (CategoryTheory.Enriched.ModuleMappingR.FreeEvaluation.rightShiftRestrictionIsoReadback d b
        S L i r X N F
      (CategoryTheory.Enriched.ModuleMappingR.FreeEvaluation.rawRightShiftRestrictionIso d b S L i
        r X N F e)).hom c =
      (CategoryTheory.Enriched.ModuleMappingR.FreeEvaluation.valueIso d b S L r X N c).hom ≫
        (ihom X).map
          ((SphereModuleMappingEnd.diagram d S L N).toEnrichedFunctor.toOrdinaryFunctor.map
          (β_ r c).hom) ≫ (ihom X).map (component e.inv c) := by
  unfold CategoryTheory.Enriched.ModuleMappingR.FreeEvaluation.rightShiftRestrictionIsoReadback
    CategoryTheory.Enriched.ModuleMappingR.FreeEvaluation.rawRightShiftRestrictionIso
  rw [Iso.trans_hom, component_comp, cotensorRestrictionIso_hom_component]
  let g : value d b S L
    (CategoryTheory.Enriched.ModuleMappingR.FreeEvaluation.freeAt d S L r X) N c ⟶
      (ihom X).obj (F.toEnrichedFunctor.obj (i.obj c)) :=
    component
      (CategoryTheory.Enriched.ModuleMappingR.FreeEvaluation.rawRightShiftDiagramIso d b S L r X N
      (restrictionObject i F) e).hom c
  change g ≫ 𝟙 ((ihom X).obj (F.toEnrichedFunctor.obj (i.obj c))) = _
  exact (Category.comp_id g).trans
    (rawRightShiftDiagramIso_hom_component d b S L r X N (restrictionObject i F) e c)

omit [SymmetricCategory I] [HasProducts.{uI} V] [HasEqualizers V] in
/-- Both input maps retain the actual full sphere action of every original source module. -/
theorem sigma_twoInputs (Y : EnrichedFunctorCat V I) (A : ExternalRightModule.Action d S Y)
    {n m a a' : I} (f : n ⟶ m) (u : a ⟶ a') :
    (Y.toEnrichedFunctor.toOrdinaryFunctor.map f ⊗ₘ S.toOrdinaryFunctor.map u) ≫
        ExternalRightModule.sigma d S Y A m a' =
      ExternalRightModule.sigma d S Y A n a ≫
        Y.toEnrichedFunctor.toOrdinaryFunctor.map (f ⊗ₘ u) := by
  let p : Y.toEnrichedFunctor.obj n ⊗ S.obj a ⟶
      Y.toEnrichedFunctor.obj (n ⊗ a) :=
    (eHomEquiv V).symm ((ExternalRightModule.external d S Y A).app (n, a))
  let p' : Y.toEnrichedFunctor.obj m ⊗ S.obj a' ⟶
      Y.toEnrichedFunctor.obj (m ⊗ a') :=
    (eHomEquiv V).symm ((ExternalRightModule.external d S Y A).app (m, a'))
  let q : Y.toEnrichedFunctor.obj n ⊗ S.obj a ⟶
      Y.toEnrichedFunctor.obj m ⊗ S.obj a' :=
    Y.toEnrichedFunctor.toOrdinaryFunctor.map f ⊗ₘ S.toOrdinaryFunctor.map u
  let k : Y.toEnrichedFunctor.obj (n ⊗ a) ⟶ Y.toEnrichedFunctor.obj (m ⊗ a') :=
    Y.toEnrichedFunctor.toOrdinaryFunctor.map (f ⊗ₘ u)
  have ht : q ≫ p' = p ≫ k :=
    Reconstruction.sphereComponent_twoInputs d S Y.toEnrichedFunctor
      (ExternalRightModule.external d S Y A) n m a a' f u
  have hp : p = ExternalRightModule.sigma d S Y A n a :=
    ExternalRightModule.external_component d S Y A n a
  have hp' : p' = ExternalRightModule.sigma d S Y A m a' :=
    ExternalRightModule.external_component d S Y A m a'
  exact (congrArg (fun z => q ≫ z) hp').symm.trans
    (ht.trans (congrArg (fun z => z ≫ k) hp))

/-- The original value comparison followed by the actual target block map. -/
def translatedValueIso (r : I) (X : V) (N : Module d S L) (c : I) :
    value d b S L (CategoryTheory.Enriched.ModuleMappingR.FreeEvaluation.freeAt d S L r X) N c ≅
      (ihom X).obj ((SphereModuleMappingEnd.diagram d S L N).toEnrichedFunctor.obj (c ⊗ r)) :=
  CategoryTheory.Enriched.ModuleMappingR.FreeEvaluation.valueIso d b S L r X N c ≪≫
    (ihom X).mapIso
      ((SphereModuleMappingEnd.diagram d S L N).toEnrichedFunctor.toOrdinaryFunctor.mapIso (β_ r c))

/-- Every original inherited action retains the complete parameter braid and shift block. -/
theorem translatedValueIso_sigma (B : EnrichedFunctor.LaxBraidedData L)
    (r : I) (X : V) (N : Module d S L) (c a : I) :
    MonoidalClosed.uncurry (moduleSigma d b S L B
      (CategoryTheory.Enriched.ModuleMappingR.FreeEvaluation.freeAt d S L r X) N c a ≫
      (translatedValueIso d b S L r X N (c ⊗ a)).hom) =
    (α_ X
      (value d b S L (CategoryTheory.Enriched.ModuleMappingR.FreeEvaluation.freeAt d S L r X) N c)
        (S.obj a)).inv ≫
      (MonoidalClosed.uncurry (translatedValueIso d b S L r X N c).hom ▷ S.obj a) ≫
      ExternalRightModule.sigma d S (SphereModuleMappingEnd.diagram d S L N)
        (SphereModuleMappingEnd.action d S L N) (c ⊗ r) a ≫
      (SphereModuleMappingEnd.diagram d S L N).toEnrichedFunctor.toOrdinaryFunctor.map
        (CategoryTheory.Enriched.SphereOperator.RightShift.blockSwap r c a).hom := by
  let Y := SphereModuleMappingEnd.diagram d S L N
  let U :=
    value d b S L (CategoryTheory.Enriched.ModuleMappingR.FreeEvaluation.freeAt d S L r X) N c
  let f := (CategoryTheory.Enriched.ModuleMappingR.FreeEvaluation.valueIso d b S L r X N c).hom
  let f' :=
    (CategoryTheory.Enriched.ModuleMappingR.FreeEvaluation.valueIso d b S L r X N (c ⊗ a)).hom
  let q : Y.toEnrichedFunctor.obj (r ⊗ c) ⟶ Y.toEnrichedFunctor.obj (c ⊗ r) :=
    Y.toEnrichedFunctor.toOrdinaryFunctor.map (β_ r c).hom
  let q' : Y.toEnrichedFunctor.obj (r ⊗ (c ⊗ a)) ⟶
      Y.toEnrichedFunctor.obj ((c ⊗ a) ⊗ r) :=
    Y.toEnrichedFunctor.toOrdinaryFunctor.map (β_ r (c ⊗ a)).hom
  let sc := ExternalRightModule.sigma d S Y (SphereModuleMappingEnd.action d S L N) (r ⊗ c) a
  let tc := ExternalRightModule.sigma d S Y (SphereModuleMappingEnd.action d S L N) (c ⊗ r) a
  let h : Y.toEnrichedFunctor.obj ((r ⊗ c) ⊗ a) ⟶
      Y.toEnrichedFunctor.obj (r ⊗ (c ⊗ a)) :=
    Y.toEnrichedFunctor.toOrdinaryFunctor.map (α_ r c a).hom
  let h' : Y.toEnrichedFunctor.obj ((c ⊗ r) ⊗ a) ⟶
      Y.toEnrichedFunctor.obj ((c ⊗ a) ⊗ r) :=
    Y.toEnrichedFunctor.toOrdinaryFunctor.map
      (CategoryTheory.Enriched.SphereOperator.RightShift.blockSwap r c a).hom
  let t : Y.toEnrichedFunctor.obj ((r ⊗ c) ⊗ a) ⟶
      Y.toEnrichedFunctor.obj ((c ⊗ r) ⊗ a) :=
    Y.toEnrichedFunctor.toOrdinaryFunctor.map ((β_ r c).hom ▷ a)
  have hs : sc ≫ t = (q ▷ S.obj a) ≫ tc := by
    let i : S.obj a ⟶ S.obj a := S.toOrdinaryFunctor.map (𝟙 a)
    let t0 : Y.toEnrichedFunctor.obj ((r ⊗ c) ⊗ a) ⟶
        Y.toEnrichedFunctor.obj ((c ⊗ r) ⊗ a) :=
      Y.toEnrichedFunctor.toOrdinaryFunctor.map ((β_ r c).hom ⊗ₘ 𝟙 a)
    have ht : (q ⊗ₘ i) ≫ tc = sc ≫ t0 :=
      sigma_twoInputs d S Y (SphereModuleMappingEnd.action d S L N) (β_ r c).hom (𝟙 a)
    have h0 : t0 = t := congrArg Y.toEnrichedFunctor.toOrdinaryFunctor.map
      (tensorHom_id (β_ r c).hom a)
    have hi : i = 𝟙 (S.obj a) := S.toOrdinaryFunctor.map_id a
    exact (congrArg (fun z => sc ≫ z) h0).symm.trans
      (ht.symm.trans ((congrArg (fun z => (q ⊗ₘ z) ≫ tc) hi).trans
        (congrArg (fun z => z ≫ tc) (tensorHom_id q (S.obj a)))))
  have hb : h ≫ q' = t ≫ h' := by
    change Y.toEnrichedFunctor.toOrdinaryFunctor.map (α_ r c a).hom ≫
      Y.toEnrichedFunctor.toOrdinaryFunctor.map (β_ r (c ⊗ a)).hom = _
    rw [← Functor.map_comp, ← Functor.map_comp]
    exact congrArg Y.toEnrichedFunctor.toOrdinaryFunctor.map
      (FreeSourceAction.Internal.blockSwap_parameter r c a).symm
  have he : MonoidalClosed.uncurry
      (moduleSigma d b S L B
        (CategoryTheory.Enriched.ModuleMappingR.FreeEvaluation.freeAt d S L r X) N c a ≫ f') =
      (α_ X U (S.obj a)).inv ≫ (MonoidalClosed.uncurry f ▷ S.obj a) ≫ sc ≫ h :=
    CategoryTheory.Enriched.ModuleMappingR.FreeEvaluation.valueIso_sigma d b S L B r X N c a
  change MonoidalClosed.uncurry
      (moduleSigma d b S L B
        (CategoryTheory.Enriched.ModuleMappingR.FreeEvaluation.freeAt d S L r X) N c a ≫
        (f' ≫ (ihom X).map q')) =
    (α_ X U (S.obj a)).inv ≫
      (MonoidalClosed.uncurry (f ≫ (ihom X).map q) ▷ S.obj a) ≫ tc ≫ h'
  calc
    _ = MonoidalClosed.uncurry
        (moduleSigma d b S L B
          (CategoryTheory.Enriched.ModuleMappingR.FreeEvaluation.freeAt d S L r X) N c a ≫
            f') ≫ q' := by
      rw [← Category.assoc, MonoidalClosed.uncurry_natural_right]
    _ = (α_ X U (S.obj a)).inv ≫ (MonoidalClosed.uncurry f ▷ S.obj a) ≫ sc ≫ h ≫ q' := by
      rw [he]
      simp only [Category.assoc]
    _ = (α_ X U (S.obj a)).inv ≫ (MonoidalClosed.uncurry f ▷ S.obj a) ≫
        sc ≫ t ≫ h' := by
      rw [hb]
    _ = (α_ X U (S.obj a)).inv ≫ (MonoidalClosed.uncurry f ▷ S.obj a) ≫
        (q ▷ S.obj a) ≫ tc ≫ h' := by
      simpa only [Category.assoc] using congrArg
        (fun z => (α_ X U (S.obj a)).inv ≫
          (MonoidalClosed.uncurry f ▷ S.obj a) ≫ z ≫ h') hs
    _ = _ := by
      rw [MonoidalClosed.uncurry_natural_right, comp_whiskerRight]
      simp only [Category.assoc]

/-- The literal carrier ISO of the actual inherited output module and original cotensor. -/
def OutputCarrierIsoType (B : EnrichedFunctor.LaxBraidedData L)
    {J : Type uJ} [EnrichedCategory V J] (i : EnrichedFunctor V I J)
    (r : I) (X : V) (N : Module d S L) (F : EnrichedFunctorCat V J) :=
  letI := ColimitMonoidal.monoidalCategory d
  letI := BraidingMonoidal.symmetricCategory d b
  letI := Closed.monoidalClosed d
  letI : MonObj (⟨S⟩ : EnrichedFunctorCat V I) := LaxMonoid.monObj d S L
  (moduleObject d b S L B
    (CategoryTheory.Enriched.ModuleMappingR.FreeEvaluation.freeAt d S L r X) N).X ≅
    restrictionObject i (cotensorObject X F)

/-- The actual original raw ISO reads as the same carrier ISO of the inherited module. -/
def outputCarrierIso (B : EnrichedFunctor.LaxBraidedData L)
    {J : Type uJ} [EnrichedCategory V J] (i : EnrichedFunctor V I J)
    (r : I) (X : V) (N : Module d S L) (F : EnrichedFunctorCat V J)
    (e : restrictionObject i F ≅
      Closed.translatedTarget d (SphereModuleMappingEnd.diagram d S L N) r) :
    OutputCarrierIsoType d b S L B i r X N F := by
  letI := ColimitMonoidal.monoidalCategory d
  letI := BraidingMonoidal.symmetricCategory d b
  letI := Closed.monoidalClosed d
  letI : MonObj (⟨S⟩ : EnrichedFunctorCat V I) := LaxMonoid.monObj d S L
  exact CategoryTheory.Enriched.ModuleMappingR.FreeEvaluation.rightShiftRestrictionIsoReadback d b
    S L i r X N F
    (CategoryTheory.Enriched.ModuleMappingR.FreeEvaluation.rawRightShiftRestrictionIso d b S L
      i r X N F e)

/-- The inherited output module retains the original full free-value and block components. -/
theorem outputCarrierIso_hom_component (B : EnrichedFunctor.LaxBraidedData L)
    {J : Type uJ} [EnrichedCategory V J] (i : EnrichedFunctor V I J)
    (r : I) (X : V) (N : Module d S L) (F : EnrichedFunctorCat V J)
    (e : restrictionObject i F ≅
      Closed.translatedTarget d (SphereModuleMappingEnd.diagram d S L N) r) (c : I) :
    letI := ColimitMonoidal.monoidalCategory d
    letI := BraidingMonoidal.symmetricCategory d b
    letI := Closed.monoidalClosed d
    letI : MonObj (⟨S⟩ : EnrichedFunctorCat V I) := LaxMonoid.monObj d S L
    component (outputCarrierIso d b S L B i r X N F e).hom c =
      (CategoryTheory.Enriched.ModuleMappingR.FreeEvaluation.valueIso d b S L r X N c).hom ≫
        (ihom X).map
          ((SphereModuleMappingEnd.diagram d S L N).toEnrichedFunctor.toOrdinaryFunctor.map
            (β_ r c).hom) ≫ (ihom X).map (component e.inv c) := by
  let := ColimitMonoidal.monoidalCategory d
  let := BraidingMonoidal.symmetricCategory d b
  let := Closed.monoidalClosed d
  let : MonObj (⟨S⟩ : EnrichedFunctorCat V I) := LaxMonoid.monObj d S L
  exact rawRightShiftRestrictionIso_hom_component d b S L i r X N F e c

/-- The literal actual output sphere action and the original moduleSigma family. -/
def OutputSigmaProperty (B : EnrichedFunctor.LaxBraidedData L)
    (r : I) (X : V) (N : Module d S L) (c a : I) : Prop :=
  letI := ColimitMonoidal.monoidalCategory d
  letI := BraidingMonoidal.symmetricCategory d b
  letI := Closed.monoidalClosed d
  letI : MonObj (⟨S⟩ : EnrichedFunctorCat V I) := LaxMonoid.monObj d S L
  ExternalRightModule.sigma d S
      (moduleObject d b S L B
        (CategoryTheory.Enriched.ModuleMappingR.FreeEvaluation.freeAt d S L r X) N).X
      (moduleObject d b S L B
        (CategoryTheory.Enriched.ModuleMappingR.FreeEvaluation.freeAt d S L r X) N).action c a =
    moduleSigma d b S L B
      (CategoryTheory.Enriched.ModuleMappingR.FreeEvaluation.freeAt d S L r X) N c a

/-- The entire selected module action is the original moduleSigma at every pair. -/
theorem outputSigma (B : EnrichedFunctor.LaxBraidedData L)
    (r : I) (X : V) (N : Module d S L) (c a : I) :
    OutputSigmaProperty d b S L B r X N c a := by
  let := ColimitMonoidal.monoidalCategory d
  let := BraidingMonoidal.symmetricCategory d b
  let := Closed.monoidalClosed d
  let : MonObj (⟨S⟩ : EnrichedFunctorCat V I) := LaxMonoid.monObj d S L
  rfl

/-- The complete original coefficient-first structure arrow,
with its actual source block inverse. -/
def sourceDeltaAction (r : I) (N : Module d S L) (c : I) :
    S.obj r ⊗ (SphereModuleMappingEnd.diagram d S L N).toEnrichedFunctor.obj c ⟶
      (SphereModuleMappingEnd.diagram d S L N).toEnrichedFunctor.obj (r ⊗ c) :=
  (β_ (S.obj r) ((SphereModuleMappingEnd.diagram d S L N).toEnrichedFunctor.obj c)).hom ≫
    ExternalRightModule.sigma d S (SphereModuleMappingEnd.diagram d S L N)
      (SphereModuleMappingEnd.action d S L N) c r ≫
    (SphereModuleMappingEnd.diagram d S L N).toEnrichedFunctor.toOrdinaryFunctor.map (β_ r c).inv

/-- The source delta value is the original free parameter inverse of the full source action,
including the original coefficient braid and inverse index block. -/
def sourceDeltaValue (r : I) (N : Module d S L) (c : I) :
    (SphereModuleMappingEnd.diagram d S L N).toEnrichedFunctor.obj c ⟶
      value d b S L
        (CategoryTheory.Enriched.ModuleMappingR.FreeEvaluation.freeAt d S L r (S.obj r)) N c :=
  (CategoryTheory.Enriched.ModuleMappingR.FreeEvaluation.parameterEquiv d b S L r (S.obj r) N c
    ((SphereModuleMappingEnd.diagram d S L N).toEnrichedFunctor.obj c)).symm
      (sourceDeltaAction d S L r N c)

/-- The whole original source delta recovers exactly the complete original coefficient action. -/
theorem sourceDeltaValue_parameter (r : I) (N : Module d S L) (c : I) :
    CategoryTheory.Enriched.ModuleMappingR.FreeEvaluation.parameterEquiv d b S L r (S.obj r) N c
      ((SphereModuleMappingEnd.diagram d S L N).toEnrichedFunctor.obj c)
      (sourceDeltaValue d b S L r N c) = sourceDeltaAction d S L r N c :=
  (CategoryTheory.Enriched.ModuleMappingR.FreeEvaluation.parameterEquiv d b S L r (S.obj r) N c
    ((SphereModuleMappingEnd.diagram d S L N).toEnrichedFunctor.obj c)).apply_symm_apply _

/-- Both original free units recover the source delta on the full original mapping projection. -/
theorem sourceDeltaValue_generator (r : I) (N : Module d S L) (c : I) :
    (CategoryTheory.Enriched.ModuleMappingR.FreeEvaluation.generatorMap d S L r (S.obj r) ▷
      (SphereModuleMappingEnd.diagram d S L N).toEnrichedFunctor.obj c) ≫
      MonoidalClosed.uncurry (sourceDeltaValue d b S L r N c ≫
        π d b S L
          (CategoryTheory.Enriched.ModuleMappingR.FreeEvaluation.freeAt d S L r (S.obj r)) N c r) =
      sourceDeltaAction d S L r N c :=
  (CategoryTheory.Enriched.ModuleMappingR.FreeEvaluation.parameterEquiv_generator d b S L r
    (S.obj r) N c
    (sourceDeltaValue d b S L r N c)).symm.trans (sourceDeltaValue_parameter d b S L r N c)

/-- The actual source delta inverse retains the original complete free-source extension. -/
theorem sourceDeltaValue_inverse (r : I) (N : Module d S L) (c : I) :
    sourceDeltaValue d b S L r N c =
      MonoidalClosed.curry (sourceDeltaAction d S L r N c) ≫
        (CategoryTheory.Enriched.ModuleMappingR.FreeEvaluation.valueIso d b S L r
          (S.obj r) N c).inv :=
  CategoryTheory.Enriched.ModuleMappingR.FreeEvaluation.parameterEquiv_symm_apply d b S L r
    (S.obj r) N c
    (sourceDeltaAction d S L r N c)

/-- The source delta under the full function comparison is the original sphere transpose,
with the actual source/inverse target blocks cancelling in their original order. -/
theorem sourceDeltaValue_translated (r : I) (N : Module d S L) (c : I) :
    sourceDeltaValue d b S L r N c ≫ (translatedValueIso d b S L r (S.obj r) N c).hom =
      MonoidalClosed.curry
        ((β_ (S.obj r) ((SphereModuleMappingEnd.diagram d S L N).toEnrichedFunctor.obj c)).hom ≫
          ExternalRightModule.sigma d S (SphereModuleMappingEnd.diagram d S L N)
            (SphereModuleMappingEnd.action d S L N) c r) := by
  let Y := SphereModuleMappingEnd.diagram d S L N
  let p := (β_ (S.obj r) (Y.toEnrichedFunctor.obj c)).hom ≫
    ExternalRightModule.sigma d S Y (SphereModuleMappingEnd.action d S L N) c r
  let q := Y.toEnrichedFunctor.toOrdinaryFunctor.map (β_ r c).hom
  let q' := Y.toEnrichedFunctor.toOrdinaryFunctor.map (β_ r c).inv
  have hq : q' ≫ q = 𝟙 (Y.toEnrichedFunctor.obj (c ⊗ r)) :=
    (Y.toEnrichedFunctor.toOrdinaryFunctor.mapIso (β_ r c)).inv_hom_id
  have hp : (p ≫ q') ≫ q = p :=
    (Category.assoc p q' q).trans ((congrArg (fun f => p ≫ f) hq).trans (Category.comp_id p))
  rw [sourceDeltaValue_inverse]
  have hAction : sourceDeltaAction d S L r N c = p ≫ q' :=
    (Category.assoc _ _ _).symm
  rw [hAction]
  change (MonoidalClosed.curry (p ≫ q') ≫
      (CategoryTheory.Enriched.ModuleMappingR.FreeEvaluation.valueIso d b S L r
        (S.obj r) N c).inv) ≫
    ((CategoryTheory.Enriched.ModuleMappingR.FreeEvaluation.valueIso d b S L r (S.obj r) N c).hom ≫
      (ihom (S.obj r)).map q) =
      MonoidalClosed.curry p
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  exact (MonoidalClosed.curry_natural_right (p ≫ q') q).symm.trans
    (congrArg MonoidalClosed.curry hp)

end CategoryTheory.Enriched.ModuleMappingR.FreeSourceAction.Mapping

namespace CategoryTheory.Enriched.ModuleMappingR.FreeSourceAction.OriginalOperator

attribute [local instance] Enriched.prodCategory
attribute [local instance] EnrichedDayKernel.ColimitMonoidal.smallestColimits
attribute [local instance] SphereModuleMappingEnd.moduleCategory
attribute [local instance] MonoidalLeftAction.monoidalOppositeLeftAction

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [SymmetricCategory V] [MonoidalClosed V]
  {I : Type uI} [Category.{vI} I] [MonoidalCategory I] [SymmetricCategory I]
  [EnrichedOrdinaryCategory V I]
  [HasColimitsOfSize.{uI, uI} V] [HasProducts.{uI} V] [HasEqualizers V]
  (d : EnrichedMonoidalCategoryData V I)
  (b : EnrichedBraidedMonoidalCategoryData V I d)
  (S : EnrichedFunctor V I V)
  (L : EnrichedFunctor.LaxMonoidalData d
    (MonoidalClosed.enrichedMonoidalCategoryDataSelf V) S)

open EnrichedDayKernel ModuleMappingR

/-- The actual original input module, with its genuine source unit and associativity proofs. -/
def moduleFor (F : EnrichedFunctorCat V (OperatorIndex d S L))
    (hF : ExternalRightModule.Transformation d S ((indexRestriction d S L).obj F))
    (hu : ExternalRightModule.SourceUnitLaw d S L ((indexRestriction d S L).obj F)
      hF)
    (ha : ExternalRightModule.SourceAssocLaw d S L ((indexRestriction d S L).obj F)
      hF) : Module d S L :=
  ExternalRightModule.rightModule d S L ((indexRestriction d S L).obj F)
    hF hu ha

omit [HasProducts.{uI} V] [HasEqualizers V] in
/-- Every original input module action is the actual full original sphere structure map. -/
theorem moduleFor_sigma (F : EnrichedFunctorCat V (OperatorIndex d S L))
    (hF : ExternalRightModule.Transformation d S ((indexRestriction d S L).obj F))
    (hσ : ∀ c a : I, (eHomEquiv V).symm (hF.app (c, a)) = rightSphereAction d S L F c a)
    (hu : ExternalRightModule.SourceUnitLaw d S L ((indexRestriction d S L).obj F)
      hF)
    (ha : ExternalRightModule.SourceAssocLaw d S L ((indexRestriction d S L).obj F)
      hF) (c a : I) :
    letI := ColimitMonoidal.monoidalCategory d
    letI : MonObj (⟨S⟩ : EnrichedFunctorCat V I) := LaxMonoid.monObj d S L
    ExternalRightModule.sigma d S (moduleFor d S L F hF hu ha).X
      (moduleFor d S L F hF hu ha).action c a = rightSphereAction d S L F c a := by
  let := ColimitMonoidal.monoidalCategory d
  let : MonObj (⟨S⟩ : EnrichedFunctorCat V I) := LaxMonoid.monObj d S L
  exact (ExternalRightModule.rightModule_sigma d S L
    ((indexRestriction d S L).obj F) hF hu ha c a).trans
      (hσ c a)

variable (B : EnrichedFunctor.LaxBraidedData L) (hsep : IsSeparator (𝟙_ V))
  (r : I) (X : V) (F : EnrichedFunctorCat V (OperatorIndex d S L))
  (hF : ExternalRightModule.Transformation d S ((indexRestriction d S L).obj F))
  (huF : ExternalRightModule.SourceUnitLaw d S L ((indexRestriction d S L).obj F)
    hF)
  (haF : ExternalRightModule.SourceAssocLaw d S L ((indexRestriction d S L).obj F)
    hF)

abbrev N := moduleFor d S L F hF huF haF
abbrev G :=
  cotensorObject X ((CategoryTheory.Enriched.SphereOperator.RightShift.shift d S L r).obj F)

variable (hG : ExternalRightModule.Transformation d S
    ((indexRestriction d S L).obj (G d S L r X F)))
  (huG : ExternalRightModule.SourceUnitLaw d S L ((indexRestriction d S L).obj (G d S L r X F))
    hG)
  (haG : ExternalRightModule.SourceAssocLaw d S L ((indexRestriction d S L).obj (G d S L r X F))
    hG)

abbrev T := moduleFor d S L (G d S L r X F) hG huG haG

variable
  (hσF : ∀ c a : I, (eHomEquiv V).symm (hF.app (c, a)) = rightSphereAction d S L F c a)
  (hσG : ∀ c a : I, (eHomEquiv V).symm (hG.app (c, a)) =
    rightSphereAction d S L (G d S L r X F) c a)

/-- The complete literal carrier ISO on the actual two original source modules. -/
def CarrierIsoType :=
  letI := ColimitMonoidal.monoidalCategory d
  letI : MonObj (⟨S⟩ : EnrichedFunctorCat V I) := LaxMonoid.monObj d S L
  (moduleObject d b S L B
    (CategoryTheory.Enriched.ModuleMappingR.FreeEvaluation.freeAt d S L r X)
      (N d S L F hF huF haF)).X ≅
    (T d S L r X F hG huG haG).X

/-- The genuine original free value, full block braid and cotensor restriction ISO. -/
def carrierIso : CarrierIsoType d b S L B r X F hF huF haF hG huG haG := by
  letI := ColimitMonoidal.monoidalCategory d
  letI : MonObj (⟨S⟩ : EnrichedFunctorCat V I) := LaxMonoid.monObj d S L
  exact Mapping.outputCarrierIso d b S L B (indexUnitFunctor d S L)
    r X (N d S L F hF huF haF)
      ((CategoryTheory.Enriched.SphereOperator.RightShift.shift d S L r).obj F)
      (CategoryTheory.Enriched.ModuleMappingR.FreeEvaluation.shiftedRestrictionIso hsep d S L F r)

/-- Every whole actual carrier component is the original translated generator evaluation. -/
theorem carrier_hom_component (c : I) :
    letI := ColimitMonoidal.monoidalCategory d
    letI : MonObj (⟨S⟩ : EnrichedFunctorCat V I) := LaxMonoid.monObj d S L
    component (carrierIso d b S L B hsep r X F hF huF haF hG huG haG).hom c =
      (Mapping.translatedValueIso d b S L r X (N d S L F hF huF haF) c).hom := by
  let := ColimitMonoidal.monoidalCategory d
  let : MonObj (⟨S⟩ : EnrichedFunctorCat V I) := LaxMonoid.monObj d S L
  have hc := Mapping.outputCarrierIso_hom_component d b S L B (indexUnitFunctor d S L)
    r X (N d S L F hF huF haF)
      ((CategoryTheory.Enriched.SphereOperator.RightShift.shift d S L r).obj F)
      (CategoryTheory.Enriched.ModuleMappingR.FreeEvaluation.shiftedRestrictionIso hsep d S L F r) c
  have he :=
    CategoryTheory.Enriched.ModuleMappingR.FreeEvaluation.shiftedRestrictionIso_inv_component d S
      L hsep F r c
  let P := (Mapping.translatedValueIso d b S L r X (N d S L F hF huF haF) c).hom
  let Q : F.toEnrichedFunctor.obj ⟨c ⊗ r⟩ ⟶ F.toEnrichedFunctor.obj ⟨c ⊗ r⟩ :=
    component
      (CategoryTheory.Enriched.ModuleMappingR.FreeEvaluation.shiftedRestrictionIso hsep d S
        L F r).inv c
  have hQ : (ihom X).map Q = 𝟙 ((ihom X).obj (F.toEnrichedFunctor.obj ⟨c ⊗ r⟩)) :=
    (congrArg (ihom X).map he).trans ((ihom X).map_id _)
  have hP : P ≫ (ihom X).map Q = P :=
    (congrArg (fun q => P ≫ q) hQ).trans (Category.comp_id P)
  have hP' :
      (CategoryTheory.Enriched.ModuleMappingR.FreeEvaluation.valueIso d b S L r X
        (N d S L F hF huF haF) c).hom ≫
        (ihom X).map
          ((SphereModuleMappingEnd.diagram d S L
            (N d S L F hF huF haF)).toEnrichedFunctor.toOrdinaryFunctor.map
            (β_ r c).hom) ≫ (ihom X).map Q = P :=
    (Category.assoc _ _ _).symm.trans hP
  exact hc.trans hP'

/-- The full original source right-action commutation of the complete carrier ISO. -/
def LinearityProperty : Prop :=
  letI := ColimitMonoidal.monoidalCategory d
  letI : MonObj (⟨S⟩ : EnrichedFunctorCat V I) := LaxMonoid.monObj d S L
  ExternalRightModule.SourceComm d S
    (moduleObject d b S L B
      (CategoryTheory.Enriched.ModuleMappingR.FreeEvaluation.freeAt d S L r X)
        (N d S L F hF huF haF)).X
    (T d S L r X F hG huG haG).X
    (moduleObject d b S L B
      (CategoryTheory.Enriched.ModuleMappingR.FreeEvaluation.freeAt d S L r X)
        (N d S L F hF huF haF)).action
    (T d S L r X F hG huG haG).action
    (carrierIso d b S L B hsep r X F hF huF haF hG huG haG).hom

include hσF hσG in
/-- The actual stock source action commutes with the original whole cotensor carrier ISO. -/
theorem carrier_linear : LinearityProperty d b S L B hsep r X F hF huF haF hG huG haG := by
  let := ColimitMonoidal.monoidalCategory d
  let : MonObj (⟨S⟩ : EnrichedFunctorCat V I) := LaxMonoid.monObj d S L
  intro c a
  apply MonoidalClosed.uncurry_injective (A := X)
  have hc := carrier_hom_component d b S L B hsep r X F hF huF haF hG huG haG c
  have hca := carrier_hom_component d b S L B hsep r X F hF huF haF hG huG haG (c ⊗ a)
  have hs := Mapping.outputSigma d b S L B r X (N d S L F hF huF haF) c a
  unfold Mapping.OutputSigmaProperty at hs
  rw [hs, hc, hca]
  rw [moduleFor_sigma d S L (G d S L r X F) hG hσG huG haG]
  have he := Mapping.translatedValueIso_sigma d b S L B r X (N d S L F hF huF haF) c a
  have ht := FreeSourceAction.Internal.cotensorSphereAction_parameter_uncurry d S L
    ((CategoryTheory.Enriched.SphereOperator.RightShift.shift d S L r).obj F) X c a
      (Mapping.translatedValueIso d b S L r X (N d S L F hF huF haF) c).hom
  rw [ht, he]
  let A := value d b S L
    (CategoryTheory.Enriched.ModuleMappingR.FreeEvaluation.freeAt d S L r X)
      (N d S L F hF huF haF) c
  let u : (X ⊗ A) ⊗ S.obj a ⟶ F.toEnrichedFunctor.obj ⟨c ⊗ r⟩ ⊗ S.obj a :=
    MonoidalClosed.uncurry
      (Mapping.translatedValueIso d b S L r X (N d S L F hF huF haF) c).hom ▷ S.obj a
  let sc : F.toEnrichedFunctor.obj ⟨c ⊗ r⟩ ⊗ S.obj a ⟶
      F.toEnrichedFunctor.obj ⟨(c ⊗ r) ⊗ a⟩ :=
    ExternalRightModule.sigma d S (SphereModuleMappingEnd.diagram d S L (N d S L F hF huF haF))
      (SphereModuleMappingEnd.action d S L (N d S L F hF huF haF)) (c ⊗ r) a
  let k : F.toEnrichedFunctor.obj ⟨(c ⊗ r) ⊗ a⟩ ⟶
      F.toEnrichedFunctor.obj ⟨(c ⊗ a) ⊗ r⟩ :=
    ((indexRestriction d S L).obj F).toEnrichedFunctor.toOrdinaryFunctor.map
      (CategoryTheory.Enriched.SphereOperator.RightShift.blockSwap r c a).hom
  have hn : sc = rightSphereAction d S L F (c ⊗ r) a :=
    moduleFor_sigma d S L F hF hσF huF haF (c ⊗ r) a
  have hShift : rightSphereAction d S L
    ((CategoryTheory.Enriched.SphereOperator.RightShift.shift d S L r).obj F) c a =
      rightSphereAction d S L F (c ⊗ r) a ≫ k :=
    FreeSourceAction.Internal.rightSphereAction_shift d S L F r c a
  have hLast : sc ≫ k = rightSphereAction d S L
      ((CategoryTheory.Enriched.SphereOperator.RightShift.shift d S L r).obj F) c a :=
    (congrArg (fun q => q ≫ k) hn).trans hShift.symm
  exact congrArg (fun q => (α_ X A (S.obj a)).inv ≫ u ≫ q) hLast

/-- The complete original stock output and actual cotensor-shift module ISO type. -/
def OutputIsoType :=
  letI := ColimitMonoidal.monoidalCategory d
  letI : MonObj (⟨S⟩ : EnrichedFunctorCat V I) := LaxMonoid.monObj d S L
  moduleObject d b S L B
    (CategoryTheory.Enriched.ModuleMappingR.FreeEvaluation.freeAt d S L r X)
      (N d S L F hF huF haF) ≅
    T d S L r X F hG huG haG

include hσF hσG in
/-- Both original carrier maps become actual stock module maps
by their proved source commutation. -/
def outputIso : OutputIsoType d b S L B r X F hF huF haF hG huG haG := by
  letI := ColimitMonoidal.monoidalCategory d
  letI : MonObj (⟨S⟩ : EnrichedFunctorCat V I) := LaxMonoid.monObj d S L
  exact RightModuleFree.isoOfCarrier (⟨S⟩ : EnrichedFunctorCat V I) _ _
    (carrierIso d b S L B hsep r X F hF huF haF hG huG haG)
    ((ExternalRightModule.comm_iff d S _ _ _ _ _).1
      (carrier_linear d b S L B hsep r X F hF huF haF hG huG haG hσF hσG))

namespace Family

/-- The literal whole function ISO from the original input structure families, before
specializing a constructed shifted target. -/
def OutputIsoType
    (t : ∀ H : EnrichedFunctorCat V (OperatorIndex d S L),
      ExternalRightModule.Transformation d S ((indexRestriction d S L).obj H))
    (hu : ∀ H : EnrichedFunctorCat V (OperatorIndex d S L),
      ExternalRightModule.SourceUnitLaw d S L ((indexRestriction d S L).obj H) (t H))
    (ha : ∀ H : EnrichedFunctorCat V (OperatorIndex d S L),
      ExternalRightModule.SourceAssocLaw d S L ((indexRestriction d S L).obj H) (t H))
    (r : I) (X : V) (F : EnrichedFunctorCat V (OperatorIndex d S L)) :=
  OriginalOperator.OutputIsoType d b S L B r X F (t F) (hu F) (ha F)
    (t (G d S L r X F)) (hu (G d S L r X F)) (ha (G d S L r X F))

/-- Construct the complete stock module ISO from actual source transformations and their
original unit/associativity and component families. No output comparison is an input. -/
def outputIso
    (t : ∀ H : EnrichedFunctorCat V (OperatorIndex d S L),
      ExternalRightModule.Transformation d S ((indexRestriction d S L).obj H))
    (hu : ∀ H : EnrichedFunctorCat V (OperatorIndex d S L),
      ExternalRightModule.SourceUnitLaw d S L ((indexRestriction d S L).obj H) (t H))
    (ha : ∀ H : EnrichedFunctorCat V (OperatorIndex d S L),
      ExternalRightModule.SourceAssocLaw d S L ((indexRestriction d S L).obj H) (t H))
    (hσ : ∀ H : EnrichedFunctorCat V (OperatorIndex d S L), ∀ c a : I,
      (eHomEquiv V).symm ((t H).app (c, a)) = rightSphereAction d S L H c a)
    (hsep : IsSeparator (𝟙_ V)) (r : I) (X : V)
    (F : EnrichedFunctorCat V (OperatorIndex d S L)) :
    OutputIsoType d b S L B t hu ha r X F :=
  OriginalOperator.outputIso d b S L B hsep r X F (t F) (hu F) (ha F)
    (t (G d S L r X F)) (hu (G d S L r X F)) (ha (G d S L r X F))
    (hσ F) (hσ (G d S L r X F))

/-- Read the entire module ISO back on its original complete module objects. -/
def outputIsoReadback
    (t : ∀ H : EnrichedFunctorCat V (OperatorIndex d S L),
      ExternalRightModule.Transformation d S ((indexRestriction d S L).obj H))
    (hu : ∀ H : EnrichedFunctorCat V (OperatorIndex d S L),
      ExternalRightModule.SourceUnitLaw d S L ((indexRestriction d S L).obj H) (t H))
    (ha : ∀ H : EnrichedFunctorCat V (OperatorIndex d S L),
      ExternalRightModule.SourceAssocLaw d S L ((indexRestriction d S L).obj H) (t H))
    (r : I) (X : V) (F : EnrichedFunctorCat V (OperatorIndex d S L))
    (e : OutputIsoType d b S L B t hu ha r X F) :
    OriginalOperator.OutputIsoType d b S L B r X F (t F) (hu F) (ha F)
      (t (G d S L r X F)) (hu (G d S L r X F)) (ha (G d S L r X F)) := e

section Equivalence

variable
  (t : ∀ H : EnrichedFunctorCat V (OperatorIndex d S L),
    ExternalRightModule.Transformation d S ((indexRestriction d S L).obj H))
  (hu : ∀ H : EnrichedFunctorCat V (OperatorIndex d S L),
    ExternalRightModule.SourceUnitLaw d S L ((indexRestriction d S L).obj H) (t H))
  (ha : ∀ H : EnrichedFunctorCat V (OperatorIndex d S L),
    ExternalRightModule.SourceAssocLaw d S L ((indexRestriction d S L).obj H) (t H))
  (hσ : ∀ H : EnrichedFunctorCat V (OperatorIndex d S L), ∀ c a : I,
    (eHomEquiv V).symm ((t H).app (c, a)) = rightSphereAction d S L H c a)
  (E : Module d S L ≌ EnrichedFunctorCat V (OperatorIndex d S L))
  (hE : ∀ H : EnrichedFunctorCat V (OperatorIndex d S L),
    OriginalOperator.moduleFor d S L H (t H) (hu H) (ha H) = E.inverse.obj H)

/-- The complete E-image of the same original function module on the actual operator carrier. -/
def NativeOutputIsoType (r : I) (X : V) (F : EnrichedFunctorCat V (OperatorIndex d S L)) :=
  E.functor.obj
    (moduleObject d b S L B (CategoryTheory.Enriched.ModuleMappingR.FreeEvaluation.freeAt d S L r X)
      (OriginalOperator.moduleFor d S L F (t F) (hu F) (ha F))) ≅ G d S L r X F

include hσ hE in
/-- The entire native output is constructed from the proved original source ISO and actual
carrier counit, using only the existing input module reconstruction family. -/
def nativeOutputIso (hsep : IsSeparator (𝟙_ V))
    (r : I) (X : V) (F : EnrichedFunctorCat V (OperatorIndex d S L)) :
    NativeOutputIsoType d b S L B t hu ha E r X F := by
  letI := ColimitMonoidal.monoidalCategory d
  letI : MonObj (⟨S⟩ : EnrichedFunctorCat V I) := LaxMonoid.monObj d S L
  exact E.functor.mapIso (outputIso d b S L B t hu ha hσ hsep r X F) ≪≫
    E.functor.mapIso (eqToIso (hE (G d S L r X F))) ≪≫ E.counitIso.app (G d S L r X F)

include hσ hE in
/-- The full native forward map retains the actual E-image of the original module map,
original input-module reconstruction and actual carrier counit. -/
theorem nativeOutputIso_hom (hsep : IsSeparator (𝟙_ V))
    (r : I) (X : V) (F : EnrichedFunctorCat V (OperatorIndex d S L)) :
    (nativeOutputIso d b S L B t hu ha hσ E hE hsep r X F).hom =
      (E.functor.map (outputIso d b S L B t hu ha hσ hsep r X F).hom ≫
        E.functor.map (eqToHom (hE (G d S L r X F)))) ≫ E.counitIso.hom.app (G d S L r X F) := by
  let := ColimitMonoidal.monoidalCategory d
  let : MonObj (⟨S⟩ : EnrichedFunctorCat V I) := LaxMonoid.monObj d S L
  simp only [nativeOutputIso, Iso.trans_hom, Functor.mapIso_hom, Category.assoc]
  rfl


include hσ hE in
/-- The native inverse uses the actual carrier counit inverse, original source reconstruction
inverse, and the whole E-image of the proved inverse module map. -/
theorem nativeOutputIso_inv (hsep : IsSeparator (𝟙_ V))
    (r : I) (X : V) (F : EnrichedFunctorCat V (OperatorIndex d S L)) :
    (nativeOutputIso d b S L B t hu ha hσ E hE hsep r X F).inv =
      E.counitIso.inv.app (G d S L r X F) ≫
        E.functor.map (eqToHom (hE (G d S L r X F)).symm) ≫
          E.functor.map (outputIso d b S L B t hu ha hσ hsep r X F).inv := by
  let := ColimitMonoidal.monoidalCategory d
  let : MonObj (⟨S⟩ : EnrichedFunctorCat V I) := LaxMonoid.monObj d S L
  simp only [nativeOutputIso, Iso.trans_inv, Functor.mapIso_inv, Category.assoc]
  rfl


/-- The original complete source evaluation comparisons on the actual E functor. -/
def EvaluationDataType :=
  letI := ColimitMonoidal.monoidalCategory d
  letI : MonObj (⟨S⟩ : EnrichedFunctorCat V I) := LaxMonoid.monObj d S L
  ∀ r : I, E.functor ⋙ EnrichedFunctorCat.evaluation (⟨r⟩ : OperatorIndex d S L) ≅
    CategoryTheory.Enriched.RightModuleFreeEvaluation.Primitive.evaluation
      (⟨S⟩ : EnrichedFunctorCat V I) r

/-- The actual original source free comparison comes from both original adjunctions and
that same complete evaluation comparison, before any native free object is expanded. -/
def sourceFreeIso (R : EvaluationDataType d S L E) (r : I) (X : V) :
    CategoryTheory.Enriched.ModuleMappingR.FreeEvaluation.freeAt d S L r X ≅
      E.inverse.obj (Free.object (⟨r⟩ : OperatorIndex d S L) X) := by
  letI := ColimitMonoidal.monoidalCategory d
  letI : MonObj (⟨S⟩ : EnrichedFunctorCat V I) := LaxMonoid.monObj d S L
  exact (FreeAdjunctionSource.comparison E (⟨r⟩ : OperatorIndex d S L)
    (CategoryTheory.Enriched.RightModuleFreeEvaluation.Primitive.free
      (⟨S⟩ : EnrichedFunctorCat V I) r)
    (CategoryTheory.Enriched.RightModuleFreeEvaluation.Primitive.evaluation
      (⟨S⟩ : EnrichedFunctorCat V I) r)
    (CategoryTheory.Enriched.RightModuleFreeEvaluation.Primitive.adjunction
      (⟨S⟩ : EnrichedFunctorCat V I) r)
    (R r)).app X

attribute [local irreducible] Closed.monoidalClosed
set_option backward.isDefEq.respectTransparency true in
/-- Every complete genuine source ISO acts by the original full source-module precomposition. -/
def sourceIso {M M' : Module d S L} (e : M ≅ M') (Q : Module d S L) :
    moduleObject d b S L B M' Q ≅ moduleObject d b S L B M Q := by
  letI := ColimitMonoidal.monoidalCategory d
  letI := BraidingMonoidal.symmetricCategory d b
  letI := Closed.monoidalClosed d
  letI : MonObj (⟨S⟩ : EnrichedFunctorCat V I) := LaxMonoid.monObj d S L
  letI := LaxMonoid.isCommMonObj d b S L B
  exact {
    hom := moduleSourceMap d b S L B e.hom Q
    inv := moduleSourceMap d b S L B e.inv Q
    hom_inv_id :=
      (moduleSourceMap_comp d b S L B e.hom e.inv Q).symm.trans
        ((congrArg (fun f => moduleSourceMap d b S L B f Q) e.inv_hom_id).trans
          (moduleSourceMap_id d b S L B M' Q))
    inv_hom_id :=
      (moduleSourceMap_comp d b S L B e.inv e.hom Q).symm.trans
        ((congrArg (fun f => moduleSourceMap d b S L B f Q) e.hom_inv_id).trans
          (moduleSourceMap_id d b S L B M Q)) }

/-- The full actual function object on an actual native free source. -/
def NativeFreeOutputIsoType (r : I) (X : V) (F : EnrichedFunctorCat V (OperatorIndex d S L)) :=
  E.functor.obj
    (moduleObject d b S L B (E.inverse.obj (Free.object (⟨r⟩ : OperatorIndex d S L) X))
      (OriginalOperator.moduleFor d S L F (t F) (hu F) (ha F))) ≅ G d S L r X F

include hσ hE in
/-- The actual native free-source function ISO retains original free/evaluation comparisons,
full Mapping_R source precomposition, the proved R-linear output and actual E counit. -/
def nativeFreeOutputIso (R : EvaluationDataType d S L E) (hsep : IsSeparator (𝟙_ V))
    (r : I) (X : V) (F : EnrichedFunctorCat V (OperatorIndex d S L)) :
    NativeFreeOutputIsoType d b S L B t hu ha E r X F := by
  letI := ColimitMonoidal.monoidalCategory d
  letI : MonObj (⟨S⟩ : EnrichedFunctorCat V I) := LaxMonoid.monObj d S L
  exact E.functor.mapIso (sourceIso d b S L B (sourceFreeIso d S L E R r X)
      (OriginalOperator.moduleFor d S L F (t F) (hu F) (ha F))) ≪≫
    nativeOutputIso d b S L B t hu ha hσ E hE hsep r X F

/-- The whole native function spectrum from an actual free coefficient unit. -/
def NativeFreeUnitOutputIsoType (r : I) (F : EnrichedFunctorCat V (OperatorIndex d S L)) :=
  E.functor.obj (moduleObject d b S L B
    (E.inverse.obj (Free.object (⟨r⟩ : OperatorIndex d S L) (𝟙_ V)))
    (OriginalOperator.moduleFor d S L F (t F) (hu F) (ha F))) ≅
    (CategoryTheory.Enriched.SphereOperator.RightShift.shift d S L r).obj F

include hσ hE in
/-- The full free S0 function identification uses the original closed unit evaluation. -/
def nativeFreeUnitOutputIso (R : EvaluationDataType d S L E) (hsep : IsSeparator (𝟙_ V))
    (r : I) (F : EnrichedFunctorCat V (OperatorIndex d S L)) :
    NativeFreeUnitOutputIsoType d b S L B t hu ha E r F :=
  nativeFreeOutputIso d b S L B t hu ha hσ E hE R hsep r (𝟙_ V) F ≪≫
    EnrichedFunctorCat.ScalarCotensorUnit.iso
      ((CategoryTheory.Enriched.SphereOperator.RightShift.shift d S L r).obj F)

/-- An actual coefficient ISO acts on the whole original scalar cotensor. -/
def coefficientCotensorIso {X Y : V} (e : X ≅ Y)
    (F : EnrichedFunctorCat V (OperatorIndex d S L)) :
    cotensorObject X F ≅ cotensorObject Y F :=
  ((ScalarLeibniz.cotensorBifunctor (V := V) (A := OperatorIndex d S L)).mapIso e.op).app F |>.symm

/-- The literal full native free function output on an actual coefficient comparison. -/
def NativeFreeCoefficientOutputIsoType (r : I) (X Y : V)
    (F : EnrichedFunctorCat V (OperatorIndex d S L)) :=
  E.functor.obj (moduleObject d b S L B
    (E.inverse.obj (Free.object (⟨r⟩ : OperatorIndex d S L) X))
    (OriginalOperator.moduleFor d S L F (t F) (hu F) (ha F))) ≅
    cotensorObject Y ((CategoryTheory.Enriched.SphereOperator.RightShift.shift d S L r).obj F)

include hσ hE in
/-- Actual source coefficient identifications retain both original cotensor maps. -/
def nativeFreeCoefficientOutputIso (R : EvaluationDataType d S L E)
    (hsep : IsSeparator (𝟙_ V)) (r : I) (X Y : V) (e : X ≅ Y)
    (F : EnrichedFunctorCat V (OperatorIndex d S L)) :
    NativeFreeCoefficientOutputIsoType d b S L B t hu ha E r X Y F :=
  nativeFreeOutputIso d b S L B t hu ha hσ E hE R hsep r X F ≪≫
    coefficientCotensorIso d S L e
      ((CategoryTheory.Enriched.SphereOperator.RightShift.shift d S L r).obj F)

/-- The exact source delta/free-generator comparison at every original source and shift degree. -/
def DeltaComponentProperty
    (q : ∀ r : I, ∀ H : EnrichedFunctorCat V (OperatorIndex d S L),
      H ⟶ cotensorObject (S.obj r)
        ((CategoryTheory.Enriched.SphereOperator.RightShift.shift d S L r).obj H))
    (r : I) (F : EnrichedFunctorCat V (OperatorIndex d S L)) (c : I) : Prop :=
  Mapping.sourceDeltaValue d b S L r
      (OriginalOperator.moduleFor d S L F (t F) (hu F) (ha F)) c ≫
    (Mapping.translatedValueIso d b S L r (S.obj r)
      (OriginalOperator.moduleFor d S L F (t F) (hu F) (ha F)) c).hom =
    component (q r F) (⟨c⟩ : OperatorIndex d S L)

include hσ in
/-- A genuine original structure-transpose family reads back as the source delta parameter
inverse, with both original free units and the full coefficient/block maps retained. -/
theorem deltaValue_component
    (q : ∀ r : I, ∀ H : EnrichedFunctorCat V (OperatorIndex d S L),
      H ⟶ cotensorObject (S.obj r)
        ((CategoryTheory.Enriched.SphereOperator.RightShift.shift d S L r).obj H))
    (hQ : ∀ r : I, ∀ H : EnrichedFunctorCat V (OperatorIndex d S L), ∀ c : I,
      component (q r H) (⟨c⟩ : OperatorIndex d S L) =
        MonoidalClosed.curry ((β_ (S.obj r) (H.toEnrichedFunctor.obj ⟨c⟩)).hom ≫
          rightSphereAction d S L H c r))
    (r : I) (F : EnrichedFunctorCat V (OperatorIndex d S L)) (c : I) :
    DeltaComponentProperty d b S L t hu ha q r F c := by
  let := ColimitMonoidal.monoidalCategory d
  let : MonObj (⟨S⟩ : EnrichedFunctorCat V I) := LaxMonoid.monObj d S L
  have hp := Mapping.sourceDeltaValue_translated d b S L r
    (OriginalOperator.moduleFor d S L F (t F) (hu F) (ha F)) c
  have hs := OriginalOperator.moduleFor_sigma d S L F (t F) (hσ F) (hu F) (ha F) c r
  let p := (β_ (S.obj r) (F.toEnrichedFunctor.obj (⟨c⟩ : OperatorIndex d S L))).hom
  have hAction := congrArg (fun f => p ≫ f) hs
  exact hp.trans ((congrArg MonoidalClosed.curry hAction).trans (hQ r F c).symm)

end Equivalence

end Family

end CategoryTheory.Enriched.ModuleMappingR.FreeSourceAction.OriginalOperator

namespace CategoryTheory.Enriched.ModuleMappingR.FreeSourceAction.Mapping.CanonicalDelta
attribute [local instance] Enriched.prodCategory EnrichedDayKernel.ColimitMonoidal.smallestColimits
attribute [local instance] SphereModuleMappingEnd.moduleCategory
attribute [local instance] MonoidalLeftAction.monoidalOppositeLeftAction
open EnrichedDayKernel ModuleMappingR
variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [SymmetricCategory V] [MonoidalClosed V]
  {I : Type uI} [Category.{vI} I] [MonoidalCategory I] [SymmetricCategory I]
  [EnrichedOrdinaryCategory V I]
  [HasColimitsOfSize.{uI, uI} V] [HasProducts.{uI} V] [HasEqualizers V]
  (d : EnrichedMonoidalCategoryData V I) (b : EnrichedBraidedMonoidalCategoryData V I d)
  (S : EnrichedFunctor V I V)
  (L : EnrichedFunctor.LaxMonoidalData d (MonoidalClosed.enrichedMonoidalCategoryDataSelf V) S)
  (B : EnrichedFunctor.LaxBraidedData L)

/-- The actual regular module of the original sphere Day monoid. -/
def regularModule : Module d S L := by
  letI := ColimitMonoidal.monoidalCategory d
  letI : MonObj (⟨S⟩ : EnrichedFunctorCat V I) := LaxMonoid.monObj d S L
  exact RightModuleFree.regularObject (⟨S⟩ : EnrichedFunctorCat V I)

/-- The full original free sphere map is the source adjoint of its coefficient identity. -/
def sphereMap (r : I) :
    CategoryTheory.Enriched.ModuleMappingR.FreeEvaluation.freeAt d S L r (S.obj r) ⟶
      regularModule d S L := by
  letI := ColimitMonoidal.monoidalCategory d
  letI : MonObj (⟨S⟩ : EnrichedFunctorCat V I) := LaxMonoid.monObj d S L
  exact ((CategoryTheory.Enriched.RightModuleFreeEvaluation.Primitive.adjunction
    (⟨S⟩ : EnrichedFunctorCat V I) r).homEquiv (S.obj r) (regularModule d S L)).symm (𝟙 (S.obj r))

omit [SymmetricCategory I] [HasProducts.{uI} V] [HasEqualizers V] in
/-- The entire original free/evaluation family returns the original sphere coefficient identity. -/
theorem sphereMap_evaluate (r : I) :
    letI := ColimitMonoidal.monoidalCategory d
    letI : MonObj (⟨S⟩ : EnrichedFunctorCat V I) := LaxMonoid.monObj d S L
    (CategoryTheory.Enriched.RightModuleFreeEvaluation.Primitive.adjunction
      (⟨S⟩ : EnrichedFunctorCat V I) r).homEquiv (S.obj r) (regularModule d S L)
      (sphereMap d S L r) = 𝟙 (S.obj r) := by
  let := ColimitMonoidal.monoidalCategory d
  let : MonObj (⟨S⟩ : EnrichedFunctorCat V I) := LaxMonoid.monObj d S L
  exact ((CategoryTheory.Enriched.RightModuleFreeEvaluation.Primitive.adjunction
    (⟨S⟩ : EnrichedFunctorCat V I) r).homEquiv (S.obj r) (regularModule d S L)).apply_symm_apply _

/-- The source Mapping_R regular-unit evaluation is an actual complete stock module ISO. -/
def regularEvaluationIso (N : Module d S L) :
    moduleObject d b S L B (regularModule d S L) N ≅ N := by
  letI := ColimitMonoidal.monoidalCategory d
  letI := BraidingMonoidal.symmetricCategory d b
  letI := Closed.monoidalClosed d
  letI : MonObj (⟨S⟩ : EnrichedFunctorCat V I) := LaxMonoid.monObj d S L
  letI := LaxMonoid.isCommMonObj d b S L B
  exact CategoryTheory.RightModuleMappingEnd.Regular.regularMappingIso
    (⟨S⟩ : EnrichedFunctorCat V I) N

section SourceConstruction
attribute [local irreducible] Closed.monoidalClosed
set_option backward.isDefEq.respectTransparency true in
/-- Original source delta is genuine Mapping_R precomposition by the complete free sphere map. -/
def sourceDelta (r : I) (N : Module d S L) :
    N ⟶ moduleObject d b S L B
      (CategoryTheory.Enriched.ModuleMappingR.FreeEvaluation.freeAt d S L r (S.obj r)) N := by
  letI := ColimitMonoidal.monoidalCategory d
  letI := BraidingMonoidal.symmetricCategory d b
  letI := Closed.monoidalClosed d
  letI : MonObj (⟨S⟩ : EnrichedFunctorCat V I) := LaxMonoid.monObj d S L
  letI := LaxMonoid.isCommMonObj d b S L B
  exact (regularEvaluationIso d b S L B N).inv ≫
    moduleSourceMap d b S L B (sphereMap d S L r) N

end SourceConstruction

end CategoryTheory.Enriched.ModuleMappingR.FreeSourceAction.Mapping.CanonicalDelta

open CategoryTheory.Enriched CategoryTheory.EnrichedFunctorCat
namespace CategoryTheory.Enriched.ModuleMappingR.FreeSourceAction.Mapping.CanonicalDelta
open CategoryTheory.RightModuleMappingEnd.Regular
attribute [local instance] Enriched.prodCategory EnrichedDayKernel.ColimitMonoidal.smallestColimits
attribute [local instance] SphereModuleMappingEnd.moduleCategory
attribute [local instance] MonoidalLeftAction.monoidalOppositeLeftAction
open EnrichedDayKernel ModuleMappingR
variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [SymmetricCategory V] [MonoidalClosed V]
  {I : Type uI} [Category.{vI} I] [MonoidalCategory I] [SymmetricCategory I]
  [EnrichedOrdinaryCategory V I]
  [HasColimitsOfSize.{uI, uI} V] [HasProducts.{uI} V] [HasEqualizers V]
  (d : EnrichedMonoidalCategoryData V I) (b : EnrichedBraidedMonoidalCategoryData V I d)
  (S : EnrichedFunctor V I V)
  (L : EnrichedFunctor.LaxMonoidalData d (MonoidalClosed.enrichedMonoidalCategoryDataSelf V) S)
  (B : EnrichedFunctor.LaxBraidedData L)

/-- The actual complete Day regular evaluation factory is its original generic source factory. -/
theorem regularEvaluationIso_factory_heq (N : Module d S L) :
    letI := ColimitMonoidal.monoidalCategory d
    letI := BraidingMonoidal.symmetricCategory d b
    letI := Closed.monoidalClosed d
    letI : MonObj (⟨S⟩ : EnrichedFunctorCat V I) := LaxMonoid.monObj d S L
    letI := LaxMonoid.isCommMonObj d b S L B
    HEq (regularEvaluationIso d b S L B N)
      (regularMappingIso
        (⟨S⟩ : EnrichedFunctorCat V I) N) := by
  let := ColimitMonoidal.monoidalCategory d
  let := BraidingMonoidal.symmetricCategory d b
  let := Closed.monoidalClosed d
  let : MonObj (⟨S⟩ : EnrichedFunctorCat V I) := LaxMonoid.monObj d S L
  let := LaxMonoid.isCommMonObj d b S L B
  rfl

/-- The original actual inverse regular evaluation carrier retains the exact source map. -/
theorem regularEvaluationIso_inverse_carrier_heq (N : Module d S L) :
    letI := ColimitMonoidal.monoidalCategory d
    letI := BraidingMonoidal.symmetricCategory d b
    letI := Closed.monoidalClosed d
    letI : MonObj (⟨S⟩ : EnrichedFunctorCat V I) := LaxMonoid.monObj d S L
    letI := LaxMonoid.isCommMonObj d b S L B
    HEq (SphereModuleMappingEnd.moduleMap d S L (regularEvaluationIso d b S L B N).inv)
      (regularMappingIso
        (⟨S⟩ : EnrichedFunctorCat V I) N).inv.hom := by
  let := ColimitMonoidal.monoidalCategory d
  let := BraidingMonoidal.symmetricCategory d b
  let := Closed.monoidalClosed d
  let : MonObj (⟨S⟩ : EnrichedFunctorCat V I) := LaxMonoid.monObj d S L
  let := LaxMonoid.isCommMonObj d b S L B
  have hM := moduleObject_eq_source d b S L B (regularModule d S L) N
  have hE := regularEvaluationIso_factory_heq d b S L B N
  exact inverseCarrier_heq
    (⟨S⟩ : EnrichedFunctorCat V I) hM _ _ hE

/-- The complete actual inverse source carrier equals its original source factory map. -/
theorem regularEvaluationIso_inverse_carrier_eq (N : Module d S L) :
    letI := ColimitMonoidal.monoidalCategory d
    letI := BraidingMonoidal.symmetricCategory d b
    letI := Closed.monoidalClosed d
    letI : MonObj (⟨S⟩ : EnrichedFunctorCat V I) := LaxMonoid.monObj d S L
    letI := LaxMonoid.isCommMonObj d b S L B
    SphereModuleMappingEnd.moduleMap d S L (regularEvaluationIso d b S L B N).inv =
      (regularMappingIso
        (⟨S⟩ : EnrichedFunctorCat V I) N).inv.hom := by
  let := ColimitMonoidal.monoidalCategory d
  let := BraidingMonoidal.symmetricCategory d b
  let := Closed.monoidalClosed d
  let : MonObj (⟨S⟩ : EnrichedFunctorCat V I) := LaxMonoid.monObj d S L
  let := LaxMonoid.isCommMonObj d b S L B
  exact eq_of_heq (regularEvaluationIso_inverse_carrier_heq d b S L B N)


/-- Both expressions are the same original actual Day action equalizer inclusion. -/
theorem actualSourceι_eq (M N : Module d S L) :
    letI := ColimitMonoidal.monoidalCategory d
    letI := BraidingMonoidal.symmetricCategory d b
    letI := Closed.monoidalClosed d
    letI : MonObj (⟨S⟩ : EnrichedFunctorCat V I) := LaxMonoid.monObj d S L
    ι d b S L M N = RightModuleMappingEnd.ι (⟨S⟩ : EnrichedFunctorCat V I) M N := by
  let := ColimitMonoidal.monoidalCategory d
  let := BraidingMonoidal.symmetricCategory d b
  let := Closed.monoidalClosed d
  let : MonObj (⟨S⟩ : EnrichedFunctorCat V I) := LaxMonoid.monObj d S L
  rfl

/-- The actual original Day mapping projection keeps the literal original stock inclusion. -/
theorem actualMappingπ_eq (M N : Module d S L) (c j : I) :
    letI := ColimitMonoidal.monoidalCategory d
    letI := BraidingMonoidal.symmetricCategory d b
    letI := Closed.monoidalClosed d
    letI : MonObj (⟨S⟩ : EnrichedFunctorCat V I) := LaxMonoid.monObj d S L
    π d b S L M N c j =
      component (RightModuleMappingEnd.ι (⟨S⟩ : EnrichedFunctorCat V I) M N) c ≫
        Closed.π d M.X N.X c j := by
  let := ColimitMonoidal.monoidalCategory d
  let := BraidingMonoidal.symmetricCategory d b
  let := Closed.monoidalClosed d
  let : MonObj (⟨S⟩ : EnrichedFunctorCat V I) := LaxMonoid.monObj d S L
  rw [π]
  change component (ι d b S L M N) c ≫ Closed.π d M.X N.X c j = _
  rw [actualSourceι_eq]
  rfl

omit [HasProducts.{uI} V] [HasEqualizers V] in
/-- The actual Day braid and inverse index braid compute the coefficient-first regular action. -/
theorem regularTranspose_point (N : Module d S L) (j c : I) :
    letI := ColimitMonoidal.monoidalCategory d
    letI := BraidingMonoidal.symmetricCategory d b
    letI : MonObj (⟨S⟩ : EnrichedFunctorCat V I) := LaxMonoid.monObj d S L
    Generators.point d.tensorEnrichedFunctor S
      (SphereModuleMappingEnd.diagram d S L N).toEnrichedFunctor (j, c) ≫
        component ((β_ (⟨S⟩ : EnrichedFunctorCat V I) N.X).hom ≫ N.action) (j ⊗ c) =
          sourceDeltaAction d S L j N c := by
  let := ColimitMonoidal.monoidalCategory d
  let := BraidingMonoidal.symmetricCategory d b
  let : MonObj (⟨S⟩ : EnrichedFunctorCat V I) := LaxMonoid.monObj d S L
  erw [component_comp]
  change Generators.point d.tensorEnrichedFunctor S
      (SphereModuleMappingEnd.diagram d S L N).toEnrichedFunctor (j, c) ≫
        component (BraidingMonoidal.braiding d b ⟨S⟩ N.X).hom (j ⊗ c) ≫
          component N.action (j ⊗ c) = _
  erw [BraidingMonoidal.braiding_hom_component]
  have hb := BraidingGenerators.unitGenerator_braid d S
    (SphereModuleMappingEnd.diagram d S L N).toEnrichedFunctor b (j, c)
  have ha := (ordinaryNatTrans N.action).naturality (β_ j c).inv
  change (Closed.tensorObject d
      (SphereModuleMappingEnd.diagram d S L N) ⟨S⟩).toEnrichedFunctor.toOrdinaryFunctor.map
        (β_ j c).inv ≫ component N.action (j ⊗ c) =
        component N.action (c ⊗ j) ≫
          (SphereModuleMappingEnd.diagram d S L N).toEnrichedFunctor.toOrdinaryFunctor.map
            (β_ j c).inv at ha
  have hp : Generators.point d.tensorEnrichedFunctor S
      (SphereModuleMappingEnd.diagram d S L N).toEnrichedFunctor (j, c) =
        AssociatorUnit.unitGenerator d.tensorEnrichedFunctor S
          (SphereModuleMappingEnd.diagram d S L N).toEnrichedFunctor (j, c) :=
    (Category.assoc _ _ _).symm
  erw [hp, ← Category.assoc, hb, Category.assoc, Category.assoc, ha]
  rw [unitGenerator_eq_point]
  simp only [sourceDeltaAction, ExternalRightModule.sigma,
    SphereModuleMappingEnd.action, Category.assoc]
  rfl

/-- The actual whole source inverse and inclusion retain their original regular factory. -/
theorem regularEvaluationIso_inv_ι (N : Module d S L) :
    letI := ColimitMonoidal.monoidalCategory d
    letI := BraidingMonoidal.symmetricCategory d b
    letI := Closed.monoidalClosed d
    letI : MonObj (⟨S⟩ : EnrichedFunctorCat V I) := LaxMonoid.monObj d S L
    letI := LaxMonoid.isCommMonObj d b S L B
    SphereModuleMappingEnd.moduleMap d S L (regularEvaluationIso d b S L B N).inv ≫
      ι d b S L (regularModule d S L) N =
        MonoidalClosed.curry ((β_ (⟨S⟩ : EnrichedFunctorCat V I) N.X).hom ≫ N.action) := by
  let := ColimitMonoidal.monoidalCategory d
  let := BraidingMonoidal.symmetricCategory d b
  let := Closed.monoidalClosed d
  let : MonObj (⟨S⟩ : EnrichedFunctorCat V I) := LaxMonoid.monObj d S L
  let := LaxMonoid.isCommMonObj d b S L B
  have hM := moduleObject_eq_source d b S L B (regularModule d S L) N
  have hE := regularEvaluationIso_factory_heq d b S L B N
  have hi : HEq (ι d b S L (regularModule d S L) N)
      (RightModuleMappingEnd.ι (⟨S⟩ : EnrichedFunctorCat V I)
        (RightModuleFree.regularObject (⟨S⟩ : EnrichedFunctorCat V I)) N) := by
    exact heq_of_eq (actualSourceι_eq d b S L (regularModule d S L) N)
  have h := inverseInclusion_eq
    (⟨S⟩ : EnrichedFunctorCat V I) hM
    (regularEvaluationIso d b S L B N)
    (regularMappingIso
      (⟨S⟩ : EnrichedFunctorCat V I) N) hE
    (ambient d S L (regularModule d S L) N) _ _ hi
  exact h.trans (regularMappingIso_inv_ι
    (⟨S⟩ : EnrichedFunctorCat V I) N)

/-- Every original source projection of regular evaluation is the original action transpose. -/
@[reassoc]
theorem regularEvaluationIso_inv_π (N : Module d S L) (c j : I) :
    component (SphereModuleMappingEnd.moduleMap d S L
      (regularEvaluationIso d b S L B N).inv) c ≫
        π d b S L (regularModule d S L) N c j =
          MonoidalClosed.curry (sourceDeltaAction d S L j N c) := by
  let := ColimitMonoidal.monoidalCategory d
  let := BraidingMonoidal.symmetricCategory d b
  let := Closed.monoidalClosed d
  let : MonObj (⟨S⟩ : EnrichedFunctorCat V I) := LaxMonoid.monObj d S L
  let := LaxMonoid.isCommMonObj d b S L B
  have h := regularEvaluationIso_inv_ι d b S L B N
  have hp := congrArg (fun t => component t c ≫ Closed.π d
    (SphereModuleMappingEnd.diagram d S L (regularModule d S L))
    (SphereModuleMappingEnd.diagram d S L N) c j) h
  rw [component_comp] at hp
  change component (SphereModuleMappingEnd.moduleMap d S L
      (regularEvaluationIso d b S L B N).inv) c ≫
    (component (ι d b S L (regularModule d S L) N) c ≫
      Closed.π d (SphereModuleMappingEnd.diagram d S L (regularModule d S L))
        (SphereModuleMappingEnd.diagram d S L N) c j) = _
  erw [← Category.assoc, hp]
  have hc := Closed.closedCurry_π d
    (SphereModuleMappingEnd.diagram d S L (regularModule d S L)) N.X N.X
      ((β_ (⟨S⟩ : EnrichedFunctorCat V I) N.X).hom ≫ N.action) c j
  exact hc.trans (congrArg MonoidalClosed.curry (regularTranspose_point d b S L N j c))

omit [SymmetricCategory I] [HasProducts.{uI} V] [HasEqualizers V] in
/-- Both original free units recover the identity sphere coefficient through the actual map. -/
theorem sphereMap_generator (r : I) :
    CategoryTheory.Enriched.ModuleMappingR.FreeEvaluation.generatorMap d S L r (S.obj r) ≫
      component (SphereModuleMappingEnd.moduleMap d S L (sphereMap d S L r)) r =
        𝟙 (S.obj r) := by
  let := ColimitMonoidal.monoidalCategory d
  let : MonObj (⟨S⟩ : EnrichedFunctorCat V I) := LaxMonoid.monObj d S L
  have h := (CategoryTheory.Enriched.RightModuleFreeEvaluation.Primitive.adjunction
    (⟨S⟩ : EnrichedFunctorCat V I) r).homEquiv_unit
      (S.obj r) (regularModule d S L) (sphereMap d S L r)
  have hg : (CategoryTheory.Enriched.RightModuleFreeEvaluation.Primitive.adjunction
      (⟨S⟩ : EnrichedFunctorCat V I) r).unit.app (S.obj r) =
        CategoryTheory.Enriched.ModuleMappingR.FreeEvaluation.generatorMap d S L r (S.obj r) := by
    erw [Adjunction.comp_unit_app, RightModuleFree.adjunction_unit]
    rfl
  rw [hg] at h
  exact h.symm.trans (sphereMap_evaluate d S L r)

/-- The whole delta carrier is original regular evaluation followed by source precomposition. -/
theorem sourceDelta_hom (r : I) (N : Module d S L) :
    SphereModuleMappingEnd.moduleMap d S L (sourceDelta d b S L B r N) =
      SphereModuleMappingEnd.moduleMap d S L (regularEvaluationIso d b S L B N).inv ≫
        pre d b S L (sphereMap d S L r) N := by
  rw [sourceDelta, SphereModuleMappingEnd.moduleMap_comp, moduleSourceMap_hom]

/-- The original free parameter equivalence evaluates stock delta to its full sphere action. -/
theorem sourceDelta_parameter (r : I) (N : Module d S L) (c : I) :
    CategoryTheory.Enriched.ModuleMappingR.FreeEvaluation.parameterEquiv d b S L r (S.obj r) N c
      ((SphereModuleMappingEnd.diagram d S L N).toEnrichedFunctor.obj c)
      (component (SphereModuleMappingEnd.moduleMap d S L (sourceDelta d b S L B r N)) c) =
        sourceDeltaAction d S L r N c := by
  rw [CategoryTheory.Enriched.ModuleMappingR.FreeEvaluation.parameterEquiv_generator,
    sourceDelta_hom,
    component_comp, Category.assoc, pre_π, ← Category.assoc,
    regularEvaluationIso_inv_π, MonoidalClosed.uncurry_pre_app,
    MonoidalClosed.uncurry_curry, ← comp_whiskerRight_assoc,
    sphereMap_generator, id_whiskerRight, Category.id_comp]

/-- Every component of the actual stock source delta is the original free parameter inverse. -/
theorem sourceDelta_component (r : I) (N : Module d S L) (c : I) :
    component (SphereModuleMappingEnd.moduleMap d S L (sourceDelta d b S L B r N)) c =
      sourceDeltaValue d b S L r N c := by
  apply
    (CategoryTheory.Enriched.ModuleMappingR.FreeEvaluation.parameterEquiv d b S L r (S.obj r) N c
    ((SphereModuleMappingEnd.diagram d S L N).toEnrichedFunctor.obj c)).injective
  rw [sourceDelta_parameter, sourceDeltaValue_parameter]

end CategoryTheory.Enriched.ModuleMappingR.FreeSourceAction.Mapping.CanonicalDelta
