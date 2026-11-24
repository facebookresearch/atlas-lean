/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module
public import MathlibExt.CategoryTheory.Enriched.ModuleMappingRFree
public import MathlibExt.CategoryTheory.Enriched.ModuleMappingRFamilies
public import MathlibExt.CategoryTheory.Enriched.FreeWeightedEnd
public import MathlibExt.CategoryTheory.Enriched.FreeWeightedEndMap
public import MathlibExt.CategoryTheory.Enriched.SphereOperatorRightTensor
public import MathlibExt.CategoryTheory.Enriched.SphereOperatorActionRecovery
public import MathlibExt.CategoryTheory.Enriched.SphereOperatorCoefficientAlgebra

/-!
# Free-source evaluation of enriched right-module mapping ends

The right-module mapping end restricts along the free-module generator and
the enriched free weighted end evaluates at its identity. The resulting
isomorphism has the literal value `[X, N(r ⊗ c)]`. It retains the complete
parameter and coefficient maps, the output action, and the source and target
naturality squares. Index braiding compares left and right translation;
restriction along the canonical operator right shift gives the cotensor
comparison. All constructions use arbitrary enriched monoidal data.
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

namespace CategoryTheory.Enriched.ModuleMappingR.FreeEvaluation

universe uV vV uI vI

attribute [local instance] Enriched.prodCategory EnrichedDayKernel.ColimitMonoidal.smallestColimits
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

/-- The actual source is the original free right module on the complete enriched free I-space. -/
abbrev freeAt (r : I) (X : V) : Module d S L := freeModule d S L (Free.object r X)

/-- Original generator restriction and full weighted-end evaluation give the literal translation. -/
def valueIso (r : I) (X : V) (N : Module d S L) (c : I) :
    value d b S L (freeAt d S L r X) N c ≅
      (ihom X).obj ((SphereModuleMappingEnd.diagram d S L N).toEnrichedFunctor.obj (r ⊗ c)) :=
  freeSourceValueIso d b S L (Free.object r X) N c ≪≫
    FreeWeightedEnd.iso r X
      (Closed.translatedTarget d (SphereModuleMappingEnd.diagram d S L N) c).toEnrichedFunctor

/-- The entire forward map retains both original constructed comparison maps. -/
theorem valueIso_hom (r : I) (X : V) (N : Module d S L) (c : I) :
    (valueIso d b S L r X N c).hom =
      (freeSourceValueIso d b S L (Free.object r X) N c).hom ≫
        FreeWeightedEnd.forward r X
          (Closed.translatedTarget d
            (SphereModuleMappingEnd.diagram d S L N) c).toEnrichedFunctor :=
  congrArg (fun q => (freeSourceValueIso d b S L (Free.object r X) N c).hom ≫ q)
    (FreeWeightedEnd.iso_hom r X _)

/-- The entire inverse retains the original full Hom extension and
module-action transpose. -/
theorem valueIso_inv (r : I) (X : V) (N : Module d S L) (c : I) :
    (valueIso d b S L r X N c).inv =
      FreeWeightedEnd.inverse r X
          (Closed.translatedTarget d (SphereModuleMappingEnd.diagram d S L N) c).toEnrichedFunctor ≫
        (freeSourceValueIso d b S L (Free.object r X) N c).inv :=
  congrArg (fun q => q ≫ (freeSourceValueIso d b S L (Free.object r X) N c).inv)
    (FreeWeightedEnd.iso_inv r X _)

/-- The original free-I unit followed by the actual free-module unit. -/
def generatorMap (r : I) (X : V) :
    X ⟶ (SphereModuleMappingEnd.diagram d S L (freeAt d S L r X)).toEnrichedFunctor.obj r :=
  (Free.adjunction (V := V) r).unit.app X ≫
    component (freeUnit d S L (Free.object r X)) r

/-- The whole forward map evaluates the original two units on the actual mapping projection. -/
theorem valueIso_generator (r : I) (X : V) (N : Module d S L) (c : I) :
    (valueIso d b S L r X N c).hom =
      π d b S L (freeAt d S L r X) N c r ≫
        (MonoidalClosed.pre (generatorMap d S L r X)).app
          ((SphereModuleMappingEnd.diagram d S L N).toEnrichedFunctor.obj (r ⊗ c)) := by
  rw [valueIso_hom, FreeWeightedEnd.forward_eq, ← Category.assoc,
    freeSourceValueIso_hom_π, Category.assoc]
  exact congrArg (fun q => π d b S L (freeAt d S L r X) N c r ≫ q)
    (NatTrans.congr_app (MonoidalClosed.pre_map
      ((Free.adjunction (V := V) r).unit.app X)
      (component (freeUnit d S L (Free.object r X)) r))
      ((SphereModuleMappingEnd.diagram d S L N).toEnrichedFunctor.obj (r ⊗ c))).symm

/-- Evaluating any whole mapping projection intertwines the genuine inherited output action. -/
theorem evaluationGenerator_sigma (B : EnrichedFunctor.LaxBraidedData L)
    (M N : Module d S L) (j : I) (X : V)
    (g : X ⟶ (SphereModuleMappingEnd.diagram d S L M).toEnrichedFunctor.obj j)
    (c a : I) :
    MonoidalClosed.uncurry (moduleSigma d b S L B M N c a ≫
      π d b S L M N (c ⊗ a) j ≫
      (MonoidalClosed.pre g).app
        ((SphereModuleMappingEnd.diagram d S L N).toEnrichedFunctor.obj (j ⊗ (c ⊗ a)))) =
    (α_ X (value d b S L M N c) (S.obj a)).inv ≫
      (MonoidalClosed.uncurry (π d b S L M N c j ≫ (MonoidalClosed.pre g).app
        ((SphereModuleMappingEnd.diagram d S L N).toEnrichedFunctor.obj (j ⊗ c))) ▷ S.obj a) ≫
      ExternalRightModule.sigma d S (SphereModuleMappingEnd.diagram d S L N)
        (SphereModuleMappingEnd.action d S L N) (j ⊗ c) a ≫
      (SphereModuleMappingEnd.diagram d S L N).toEnrichedFunctor.toOrdinaryFunctor.map
        (α_ j c a).hom := by
  rw [← Category.assoc (moduleSigma d b S L B M N c a)
    (π d b S L M N (c ⊗ a) j)
    ((MonoidalClosed.pre g).app
      ((SphereModuleMappingEnd.diagram d S L N).toEnrichedFunctor.obj (j ⊗ (c ⊗ a)))),
    MonoidalClosed.uncurry_pre_app
      ((SphereModuleMappingEnd.diagram d S L N).toEnrichedFunctor.obj (j ⊗ (c ⊗ a)))
      (moduleSigma d b S L B M N c a ≫ π d b S L M N (c ⊗ a) j) g,
    moduleSigma_π,
    associator_inv_naturality_left_assoc]
  simp only [MonoidalClosed.uncurry_pre_app, comp_whiskerRight, Category.assoc]

/-- The full free-source value comparison retains target coefficient action and index associator. -/
theorem valueIso_sigma (B : EnrichedFunctor.LaxBraidedData L)
    (r : I) (X : V) (N : Module d S L) (c a : I) :
    MonoidalClosed.uncurry (moduleSigma d b S L B (freeAt d S L r X) N c a ≫
      (valueIso d b S L r X N (c ⊗ a)).hom) =
    (α_ X (value d b S L (freeAt d S L r X) N c) (S.obj a)).inv ≫
      (MonoidalClosed.uncurry (valueIso d b S L r X N c).hom ▷ S.obj a) ≫
      ExternalRightModule.sigma d S (SphereModuleMappingEnd.diagram d S L N)
        (SphereModuleMappingEnd.action d S L N) (r ⊗ c) a ≫
      (SphereModuleMappingEnd.diagram d S L N).toEnrichedFunctor.toOrdinaryFunctor.map
        (α_ r c a).hom := by
  simpa only [valueIso_generator] using
    evaluationGenerator_sigma d b S L B (freeAt d S L r X) N r X
      (generatorMap d S L r X) c a

/-- The inverse recovers every complete original free-I family projection. -/
@[reassoc]
theorem valueIso_inv_restriction (r : I) (X : V) (N : Module d S L) (c j : I) :
    (valueIso d b S L r X N c).inv ≫
        π d b S L (freeAt d S L r X) N c j ≫
        (MonoidalClosed.pre (component (freeUnit d S L (Free.object r X)) j)).app
          ((SphereModuleMappingEnd.diagram d S L N).toEnrichedFunctor.obj (j ⊗ c)) =
      FreeWeightedEnd.inverse r X
          (Closed.translatedTarget d (SphereModuleMappingEnd.diagram d S L N) c).toEnrichedFunctor ≫
        Closed.π d (Free.object r X) (SphereModuleMappingEnd.diagram d S L N) c j := by
  rw [valueIso_inv, Category.assoc, ← freeSourceValueIso_hom_π]
  simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]

/-- Each unrestricted enrichment-base parameter uses the same two original Hom functions. -/
def parameterEquiv (r : I) (X : V) (N : Module d S L) (c : I) (P : V) :
    (P ⟶ value d b S L (freeAt d S L r X) N c) ≃
      (X ⊗ P ⟶ (SphereModuleMappingEnd.diagram d S L N).toEnrichedFunctor.obj (r ⊗ c)) :=
  ((Iso.refl P).homCongr (valueIso d b S L r X N c)).trans
    ((ihom.adjunction X).homEquiv P _).symm

/-- Parameter evaluation is the actual closed uncurry of the original value comparison. -/
theorem parameterEquiv_apply (r : I) (X : V) (N : Module d S L) (c : I) {P : V}
    (f : P ⟶ value d b S L (freeAt d S L r X) N c) :
    parameterEquiv d b S L r X N c P f =
      MonoidalClosed.uncurry (f ≫ (valueIso d b S L r X N c).hom) := by
  change MonoidalClosed.uncurry
    ((Iso.refl P).inv ≫ f ≫ (valueIso d b S L r X N c).hom) = _
  rw [Iso.refl_inv, Category.id_comp]

/-- The whole parameter extension is the actual original curry followed by the inverse map. -/
theorem parameterEquiv_symm_apply (r : I) (X : V) (N : Module d S L) (c : I) {P : V}
    (q : X ⊗ P ⟶ (SphereModuleMappingEnd.diagram d S L N).toEnrichedFunctor.obj (r ⊗ c)) :
    (parameterEquiv d b S L r X N c P).symm q =
      MonoidalClosed.curry q ≫ (valueIso d b S L r X N c).inv := by
  change (Iso.refl P).hom ≫ MonoidalClosed.curry q ≫
    (valueIso d b S L r X N c).inv = _
  rw [Iso.refl_hom, Category.id_comp]

/-- Every parameter is evaluated at the full original free-module generator. -/
theorem parameterEquiv_generator (r : I) (X : V) (N : Module d S L) (c : I) {P : V}
    (f : P ⟶ value d b S L (freeAt d S L r X) N c) :
    parameterEquiv d b S L r X N c P f =
      (generatorMap d S L r X ▷ P) ≫
        MonoidalClosed.uncurry (f ≫ π d b S L (freeAt d S L r X) N c r) := by
  rw [parameterEquiv_apply, valueIso_generator, ← Category.assoc,
    MonoidalClosed.uncurry_pre_app]

/-- Both original parameter functions recover every whole source-value arrow. -/
theorem parameterEquiv_left_inv (r : I) (X : V) (N : Module d S L) (c : I) {P : V}
    (f : P ⟶ value d b S L (freeAt d S L r X) N c) :
    (parameterEquiv d b S L r X N c P).symm
      (parameterEquiv d b S L r X N c P f) = f :=
  (parameterEquiv d b S L r X N c P).symm_apply_apply f

/-- Both original parameter functions recover every whole coefficient-valued evaluation. -/
theorem parameterEquiv_right_inv (r : I) (X : V) (N : Module d S L) (c : I) {P : V}
    (q : X ⊗ P ⟶ (SphereModuleMappingEnd.diagram d S L N).toEnrichedFunctor.obj (r ⊗ c)) :
    parameterEquiv d b S L r X N c P
      ((parameterEquiv d b S L r X N c P).symm q) = q :=
  (parameterEquiv d b S L r X N c P).apply_symm_apply q

/-- Every parameter arrow retains actual left coefficient tensoring before evaluation. -/
theorem parameterEquiv_regrade (r : I) (X : V) (N : Module d S L) (c : I)
    {P Q : V} (h : P ⟶ Q) (f : Q ⟶ value d b S L (freeAt d S L r X) N c) :
    parameterEquiv d b S L r X N c P (h ≫ f) =
      (X ◁ h) ≫ parameterEquiv d b S L r X N c Q f := by
  rw [parameterEquiv_apply, Category.assoc, MonoidalClosed.uncurry_natural_left,
    parameterEquiv_apply]

/-- The complete source family retains all enriched enriched Hom naturality. -/
abbrev familyEquiv (r : I) (X : V) (N : Module d S L) (c : I) (P : V) :=
  freeValueParameterEquiv d b S L (Free.object r X) N c P

/-- Every original free-source family component is the complete source restriction projection. -/
theorem familyEquiv_app (r : I) (X : V) (N : Module d S L) (c : I) {P : V}
    (f : P ⟶ value d b S L (freeAt d S L r X) N c) (j : I) :
    (familyEquiv d b S L r X N c P f).app j =
      f ≫ π d b S L (freeAt d S L r X) N c j ≫
        (MonoidalClosed.pre (component (freeUnit d S L (Free.object r X)) j)).app
          ((SphereModuleMappingEnd.diagram d S L N).toEnrichedFunctor.obj (j ⊗ c)) := by
  rw [freeValueParameterEquiv_app, Category.assoc, freeSourceValueIso_hom_π]

/-- The original whole source diagram map acts through its unchanged free-module map. -/
theorem freeSource_sourceMap {F F' : EnrichedFunctorCat V I} (f : F' ⟶ F)
    (N : Module d S L) :
    pre d b S L (freeMap d S L f) N ≫ (freeSourceIso d b S L F' N).hom =
      (freeSourceIso d b S L F N).hom ≫
        Closed.pre d f (SphereModuleMappingEnd.diagram d S L N) := by
  let := ColimitMonoidal.monoidalCategory d
  let := BraidingMonoidal.symmetricCategory d b
  let := Closed.monoidalClosed d
  let : MonObj (⟨S⟩ : EnrichedFunctorCat V I) := LaxMonoid.monObj d S L
  have h := RightModuleMappingEnd.freeSourceForward_naturality_source
    (⟨S⟩ : EnrichedFunctorCat V I) f N
  exact h.trans (congrArg (fun q => (freeSourceIso d b S L F N).hom ≫ q)
    (Closed.closedPre_eq d f (SphereModuleMappingEnd.diagram d S L N)))

/-- Every complete original source arrow retains generator restriction and full free evaluation. -/
theorem valueIso_sourceArrow (r s : I) (X Y : V)
    (f : freeAt d S L s Y ⟶ freeAt d S L r X) (N : Module d S L) (c : I) :
    component (pre d b S L f N) c ≫ (valueIso d b S L s Y N c).hom =
      valueι d b S L (freeAt d S L r X) N c ≫
        component (Closed.pre d
          (freeUnit d S L (Free.object s Y) ≫ SphereModuleMappingEnd.moduleMap d S L f)
          (SphereModuleMappingEnd.diagram d S L N)) c ≫
        FreeWeightedEnd.forward s Y
          (Closed.translatedTarget d
            (SphereModuleMappingEnd.diagram d S L N) c).toEnrichedFunctor :=
    by
  have h := congrArg (fun q => component q c)
    (freeSourceIso_sourceArrow d b S L f N)
  rw [component_comp, component_comp] at h
  rw [valueIso_hom, ← Category.assoc]
  exact (congrArg (fun q => q ≫ FreeWeightedEnd.forward s Y
    (Closed.translatedTarget d
      (SphereModuleMappingEnd.diagram d S L N) c).toEnrichedFunctor) h).trans
      (Category.assoc _ _ _)


/-- The original parameter diagram retains the literal left insertion and full tensor action. -/
abbrev parameterTarget (Y : EnrichedFunctorCat V I) (r : I) : EnrichedFunctorCat V I :=
  restrictionObject
    ((ExternalTensorMappingEndAdjunction.fixedLeftPair (V := V) r).comp V d.tensorEnrichedFunctor) Y

omit [SymmetricCategory I] [HasColimitsOfSize.{uI, uI} V]
  [HasProducts.{uI} V] [HasEqualizers V] in
/-- The complete left-inserted Hom keeps all three original composition factors. -/
theorem parameterTarget_map (Y : EnrichedFunctorCat V I) (r c c' : I) :
    (parameterTarget d Y r).toEnrichedFunctor.map c c' =
      Closed.parameterComponent d Y c c' r := Category.assoc _ _ _

omit [SymmetricCategory I] [HasColimitsOfSize.{uI, uI} V] in
/-- The full parameter Hom commutes with original weighted-end evaluation at every pair. -/
theorem weightedForward_parameter (r : I) (X : V) (Y : EnrichedFunctorCat V I) (c c' : I) :
    MonoidalClosed.uncurry ((Closed.rightObject d (Free.object r X) Y).toEnrichedFunctor.map c c') ≫
        FreeWeightedEnd.forward r X (Closed.translatedTarget d Y c').toEnrichedFunctor =
      (FreeWeightedEnd.forward r X (Closed.translatedTarget d Y c).toEnrichedFunctor ⊗ₘ
        Closed.parameterComponent d Y c c' r) ≫
        eComp V X (Y.toEnrichedFunctor.obj (r ⊗ c)) (Y.toEnrichedFunctor.obj (r ⊗ c')) := by
  simp only [FreeWeightedEnd.forward_eq]
  rw [← Category.assoc, Closed.rightObject_map_π, Category.assoc]
  have h := MappingCompositionAlgebra.parameter_pre X
    ((Free.object r X).toEnrichedFunctor.obj r)
    (Y.toEnrichedFunctor.obj (r ⊗ c)) (Y.toEnrichedFunctor.obj (r ⊗ c'))
    ((Free.adjunction (V := V) r).unit.app X)
    (Closed.π d (Free.object r X) Y c r) (Closed.parameterComponent d Y c c' r)
  rw [MonoidalClosed.enrichedOrdinaryCategorySelf_eHomWhiskerRight,
    MonoidalClosed.enrichedOrdinaryCategorySelf_eHomWhiskerRight] at h
  exact h.symm

/-- Each entire Mapping_R parameter Hom is preserved by the original free-value comparison. -/
theorem valueIso_parameter (r : I) (X : V) (N : Module d S L) (c c' : I) :
    parameterAction d b S L (freeAt d S L r X) N c c' ≫
        (valueIso d b S L r X N c').hom =
      ((valueIso d b S L r X N c).hom ⊗ₘ
        Closed.parameterComponent d (SphereModuleMappingEnd.diagram d S L N) c c' r) ≫
        eComp V X
          ((SphereModuleMappingEnd.diagram d S L N).toEnrichedFunctor.obj (r ⊗ c))
          ((SphereModuleMappingEnd.diagram d S L N).toEnrichedFunctor.obj (r ⊗ c')) := by
  let R := (freeSourceValueIso d b S L (Free.object r X) N c).hom
  let R' := (freeSourceValueIso d b S L (Free.object r X) N c').hom
  let W := FreeWeightedEnd.forward r X
    (Closed.translatedTarget d (SphereModuleMappingEnd.diagram d S L N) c).toEnrichedFunctor
  let W' := FreeWeightedEnd.forward r X
    (Closed.translatedTarget d (SphereModuleMappingEnd.diagram d S L N) c').toEnrichedFunctor
  let H := Closed.parameterComponent d (SphereModuleMappingEnd.diagram d S L N) c c' r
  let A := MonoidalClosed.uncurry
    ((Closed.rightObject d (Free.object r X)
      (SphereModuleMappingEnd.diagram d S L N)).toEnrichedFunctor.map c c')
  let E := eComp V X
    ((SphereModuleMappingEnd.diagram d S L N).toEnrichedFunctor.obj (r ⊗ c))
    ((SphereModuleMappingEnd.diagram d S L N).toEnrichedFunctor.obj (r ⊗ c'))
  have hp : (R ⊗ₘ 𝟙 (c ⟶[V] c')) ≫ (W ⊗ₘ H) =
      (valueIso d b S L r X N c).hom ⊗ₘ H := by
    exact (tensorHom_comp_tensorHom R _ W H).trans
      ((congrArg (fun q => (R ≫ W) ⊗ₘ q) (Category.id_comp H)).trans
        (congrArg (fun q => q ⊗ₘ H) (valueIso_hom d b S L r X N c).symm))
  calc
    _ = parameterAction d b S L (freeAt d S L r X) N c c' ≫ (R' ≫ W') :=
      congrArg (fun q => parameterAction d b S L (freeAt d S L r X) N c c' ≫ q)
        (valueIso_hom d b S L r X N c')
    _ = (R ⊗ₘ 𝟙 (c ⟶[V] c')) ≫ (A ≫ W') :=
      (Category.assoc _ _ _).symm.trans
        ((congrArg (fun q => q ≫ W')
          (freeSourceIso_parameter d b S L (Free.object r X) N c c')).trans
            (Category.assoc _ _ _))
    _ = (R ⊗ₘ 𝟙 (c ⟶[V] c')) ≫ ((W ⊗ₘ H) ≫ E) :=
      congrArg (fun q => (R ⊗ₘ 𝟙 (c ⟶[V] c')) ≫ q)
        (weightedForward_parameter d r X (SphereModuleMappingEnd.diagram d S L N) c c')
    _ = _ := (Category.assoc _ _ _).symm.trans (congrArg (fun q => q ≫ E) hp)

omit [SymmetricCategory I] [HasColimitsOfSize.{uI, uI} V]
  [HasProducts.{uI} V] [HasEqualizers V] in
/-- The actual scalar cotensor uses the same whole translated parameter Hom. -/
theorem parameterCotensor_action (r : I) (X : V) (Y : EnrichedFunctorCat V I) (c c' : I) :
    MonoidalClosed.uncurry
      ((cotensorObject X (parameterTarget d Y r)).toEnrichedFunctor.map c c') =
      (𝟙 ((ihom X).obj (Y.toEnrichedFunctor.obj (r ⊗ c))) ⊗ₘ
        Closed.parameterComponent d Y c c' r) ≫
        eComp V X (Y.toEnrichedFunctor.obj (r ⊗ c)) (Y.toEnrichedFunctor.obj (r ⊗ c')) := by
  rw [EnrichedFunctor.cotensor_map, parameterTarget_map,
    MonoidalClosed.uncurry_natural_left, MonoidalClosed.uncurry_curry, id_tensorHom]
  rfl

/-- The actual raw free-function diagram is the full original scalar cotensor
of left translation. -/
def diagramIso (r : I) (X : V) (N : Module d S L) :
    diagram d b S L (freeAt d S L r X) N ≅
      cotensorObject X (parameterTarget d (SphereModuleMappingEnd.diagram d S L N) r) :=
  isoOfComponents _ _ (fun c => valueIso d b S L r X N c) (by
    intro c c'
    let P := (valueIso d b S L r X N c).hom
    let H := Closed.parameterComponent d (SphereModuleMappingEnd.diagram d S L N) c c' r
    let E := eComp V X
      ((SphereModuleMappingEnd.diagram d S L N).toEnrichedFunctor.obj (r ⊗ c))
      ((SphereModuleMappingEnd.diagram d S L N).toEnrichedFunctor.obj (r ⊗ c'))
    have hp : (P ⊗ₘ 𝟙 (c ⟶[V] c')) ≫
        (𝟙 ((ihom X).obj ((SphereModuleMappingEnd.diagram d S L N).toEnrichedFunctor.obj
          (r ⊗ c))) ⊗ₘ H) = P ⊗ₘ H := by
      simp only [tensorHom_comp_tensorHom, Category.comp_id, Category.id_comp]
    have h := congrArg (fun q => (P ⊗ₘ 𝟙 (c ⟶[V] c')) ≫ q)
      (parameterCotensor_action d r X (SphereModuleMappingEnd.diagram d S L N) c c')
    have ht := h.trans ((Category.assoc (P ⊗ₘ 𝟙 (c ⟶[V] c'))
      (𝟙 ((ihom X).obj ((SphereModuleMappingEnd.diagram d S L N).toEnrichedFunctor.obj
        (r ⊗ c))) ⊗ₘ H) E).symm.trans (congrArg (fun q => q ≫ E) hp))
    exact (valueIso_parameter d b S L r X N c c').trans ht.symm)


/-- Every whole diagram forward component is the same original generator/evaluation map. -/
theorem diagramIso_hom_component (r : I) (X : V) (N : Module d S L) (c : I) :
    component (diagramIso d b S L r X N).hom c = (valueIso d b S L r X N c).hom :=
  isoOfComponents_hom_component _ _ _ _ c

/-- Every whole diagram inverse component is the same original full free extension. -/
theorem diagramIso_inv_component (r : I) (X : V) (N : Module d S L) (c : I) :
    component (diagramIso d b S L r X N).inv c = (valueIso d b S L r X N c).inv :=
  isoOfComponents_inv_component _ _ _ _ c

/-- The original left-inserted enriched tensor index functor. -/
abbrev leftIndex (r : I) : EnrichedFunctor V I I :=
  (ExternalTensorMappingEndAdjunction.fixedLeftPair (V := V) r).comp V d.tensorEnrichedFunctor
/-- The original right-inserted enriched tensor index functor. -/
abbrev rightIndex (r : I) : EnrichedFunctor V I I := Closed.rightTranslationIndex d r

omit [MonoidalClosed V] [MonoidalCategory I] [SymmetricCategory I]
  [HasColimitsOfSize.{uI, uI} V] [HasProducts.{uI} V] [HasEqualizers V] in
/-- The original full Hom block braid swaps the unchanged enriched identity insertion. -/
theorem pairSwap (r c c' : I) :
    (ExternalTensorMappingEndAdjunction.fixedLeftPair (V := V) r).map c c' ≫
      (β_ (r ⟶[V] r) (c ⟶[V] c')).hom =
    (ExternalTensorMappingEndAdjunction.fixedRightPair (V := V) r).map c c' := by
  change ((λ_ (c ⟶[V] c')).inv ≫
    (eId V r ⊗ₘ 𝟙 (c ⟶[V] c'))) ≫ (β_ (r ⟶[V] r) (c ⟶[V] c')).hom = _
  rw [Category.assoc, braiding_naturality, ← Category.assoc,
    leftUnitor_inv_braiding]
  rfl

omit [MonoidalClosed V] [HasColimitsOfSize.{uI, uI} V]
  [HasProducts.{uI} V] [HasEqualizers V] in
include b in
/-- The actual index braiding is natural on the entire original enriched Hom. -/
theorem leftRightIndex_braid (r c c' : I) :
    (leftIndex d r).map c c' ≫ eHomWhiskerLeft V (r ⊗ c) (β_ r c').hom =
      (rightIndex d r).map c c' ≫ eHomWhiskerRight V (β_ r c).hom (c' ⊗ r) := by
  have h := unitGradedNaturality_eq_whisker (d.tensorMap r r c c')
    ((β_ (r ⟶[V] r) (c ⟶[V] c')).hom ≫ d.tensorMap c c' r r)
    (β_ r c).hom (β_ r c').hom (b.braidingNaturality r r c c')
  have h' := congrArg (fun q =>
    (ExternalTensorMappingEndAdjunction.fixedLeftPair (V := V) r).map c c' ≫ q) h
  have hs := congrArg (fun q => q ≫ d.tensorMap c c' r r ≫
    eHomWhiskerRight V (β_ r c).hom (c' ⊗ r)) (pairSwap r c c')
  simp only [Category.assoc] at h' hs
  change ((ExternalTensorMappingEndAdjunction.fixedLeftPair (V := V) r).map c c' ≫
    d.tensorMap r r c c') ≫ eHomWhiskerLeft V (r ⊗ c) (β_ r c').hom =
    ((ExternalTensorMappingEndAdjunction.fixedRightPair (V := V) r).map c c' ≫
      d.tensorMap c c' r r) ≫ eHomWhiskerRight V (β_ r c).hom (c' ⊗ r)
  simpa only [Category.assoc] using h'.trans hs


omit [SymmetricCategory V] [MonoidalCategory I] [SymmetricCategory I]
  [HasColimitsOfSize.{uI, uI} V] [HasProducts.{uI} V] [HasEqualizers V] in
/-- Full target composition is preserved by the actual original enriched diagram. -/
theorem fullPost (Y : EnrichedFunctorCat V I) (i j k : I) (f : j ⟶ k) :
    eHomWhiskerLeft V i f ≫ Y.toEnrichedFunctor.map i k =
      Y.toEnrichedFunctor.map i j ≫
        eHomWhiskerLeft V (Y.toEnrichedFunctor.obj i)
          (Y.toEnrichedFunctor.toOrdinaryFunctor.map f) := by
  let H := i ⟶[V] j
  let K : V := (ihom (Y.toEnrichedFunctor.obj i)).obj (Y.toEnrichedFunctor.obj j)
  let p := eHomEquiv V f ≫ Y.toEnrichedFunctor.map j k
  have hp : p = eHomEquiv V (Y.toEnrichedFunctor.toOrdinaryFunctor.map f) :=
    (EnrichedFunctor.toOrdinaryFunctor_map Y.toEnrichedFunctor f).symm
  have hPair : (H ◁ eHomEquiv V f) ≫
      (Y.toEnrichedFunctor.map i j ⊗ₘ Y.toEnrichedFunctor.map j k) =
      Y.toEnrichedFunctor.map i j ⊗ₘ p := by
    simpa only [p, Category.comp_id, Category.id_comp, id_tensorHom] using
      tensorHom_comp_tensorHom (𝟙 H) (eHomEquiv V f)
        (Y.toEnrichedFunctor.map i j) (Y.toEnrichedFunctor.map j k)
  have hUnit : (ρ_ H).inv ≫ (Y.toEnrichedFunctor.map i j ⊗ₘ p) =
      Y.toEnrichedFunctor.map i j ≫ (ρ_ K).inv ≫ (K ◁ p) :=
    rightUnitor_inv_comp_tensorHom (Y.toEnrichedFunctor.map i j) p
  change ((ρ_ H).inv ≫ (H ◁ eHomEquiv V f) ≫ eComp V i j k) ≫
    Y.toEnrichedFunctor.map i k = _
  rw [Category.assoc, Category.assoc, Y.toEnrichedFunctor.map_comp,
    ← Category.assoc (H ◁ eHomEquiv V f), hPair]
  rw [← Category.assoc (ρ_ H).inv, hUnit, Category.assoc, Category.assoc]
  exact congrArg (fun q => Y.toEnrichedFunctor.map i j ≫ q)
    (congrArg (fun q => (ρ_ K).inv ≫ (K ◁ q) ≫
      eComp V (Y.toEnrichedFunctor.obj i) (Y.toEnrichedFunctor.obj j)
        (Y.toEnrichedFunctor.obj k)) hp)

omit [SymmetricCategory V] [MonoidalCategory I] [SymmetricCategory I]
  [HasColimitsOfSize.{uI, uI} V] [HasProducts.{uI} V] [HasEqualizers V] in
/-- Full source composition is preserved by the actual original enriched diagram. -/
theorem fullPre (Y : EnrichedFunctorCat V I) (i j k : I) (f : i ⟶ j) :
    eHomWhiskerRight V f k ≫ Y.toEnrichedFunctor.map i k =
      Y.toEnrichedFunctor.map j k ≫
        eHomWhiskerRight V (Y.toEnrichedFunctor.toOrdinaryFunctor.map f)
          (Y.toEnrichedFunctor.obj k) := by
  let H := j ⟶[V] k
  let K : V := (ihom (Y.toEnrichedFunctor.obj j)).obj (Y.toEnrichedFunctor.obj k)
  let p := eHomEquiv V f ≫ Y.toEnrichedFunctor.map i j
  have hp : p = eHomEquiv V (Y.toEnrichedFunctor.toOrdinaryFunctor.map f) :=
    (EnrichedFunctor.toOrdinaryFunctor_map Y.toEnrichedFunctor f).symm
  have hPair : (eHomEquiv V f ▷ H) ≫
      (Y.toEnrichedFunctor.map i j ⊗ₘ Y.toEnrichedFunctor.map j k) =
      p ⊗ₘ Y.toEnrichedFunctor.map j k := by
    simpa only [p, Category.id_comp, tensorHom_id] using
      tensorHom_comp_tensorHom (eHomEquiv V f) (𝟙 H)
        (Y.toEnrichedFunctor.map i j) (Y.toEnrichedFunctor.map j k)
  have hUnit : (λ_ H).inv ≫ (p ⊗ₘ Y.toEnrichedFunctor.map j k) =
      Y.toEnrichedFunctor.map j k ≫ (λ_ K).inv ≫ (p ▷ K) :=
    leftUnitor_inv_comp_tensorHom p (Y.toEnrichedFunctor.map j k)
  change ((λ_ H).inv ≫ (eHomEquiv V f ▷ H) ≫ eComp V i j k) ≫
    Y.toEnrichedFunctor.map i k = _
  rw [Category.assoc, Category.assoc, Y.toEnrichedFunctor.map_comp,
    ← Category.assoc (eHomEquiv V f ▷ H), hPair]
  rw [← Category.assoc (λ_ H).inv, hUnit, Category.assoc, Category.assoc]
  exact congrArg (fun q => Y.toEnrichedFunctor.map j k ≫ q)
    (congrArg (fun q => (λ_ K).inv ≫ (q ▷ K) ≫
      eComp V (Y.toEnrichedFunctor.obj i) (Y.toEnrichedFunctor.obj j)
        (Y.toEnrichedFunctor.obj k)) hp)



omit [HasColimitsOfSize.{uI, uI} V] [HasProducts.{uI} V] [HasEqualizers V] in
include b in
/-- The complete original target and source Hom maps preserve the translated index braiding. -/
theorem translatedBraid_whisker (Y : EnrichedFunctorCat V I) (r c c' : I) :
    (restrictionObject (leftIndex d r) Y).toEnrichedFunctor.map c c' ≫
        eHomWhiskerLeft V (Y.toEnrichedFunctor.obj (r ⊗ c))
          (Y.toEnrichedFunctor.toOrdinaryFunctor.map (β_ r c').hom) =
      (restrictionObject (rightIndex d r) Y).toEnrichedFunctor.map c c' ≫
        eHomWhiskerRight V (Y.toEnrichedFunctor.toOrdinaryFunctor.map (β_ r c).hom)
          (Y.toEnrichedFunctor.obj (c' ⊗ r)) := by
  have hi := leftRightIndex_braid d b r c c'
  have hp := fullPost Y (r ⊗ c) (r ⊗ c') (c' ⊗ r) (β_ r c').hom
  have hq := fullPre Y (r ⊗ c) (c ⊗ r) (c' ⊗ r) (β_ r c).hom
  change ((leftIndex d r).map c c' ≫ Y.toEnrichedFunctor.map (r ⊗ c) (r ⊗ c')) ≫
      eHomWhiskerLeft V (Y.toEnrichedFunctor.obj (r ⊗ c))
        (Y.toEnrichedFunctor.toOrdinaryFunctor.map (β_ r c').hom) =
    ((rightIndex d r).map c c' ≫ Y.toEnrichedFunctor.map (c ⊗ r) (c' ⊗ r)) ≫
      eHomWhiskerRight V (Y.toEnrichedFunctor.toOrdinaryFunctor.map (β_ r c).hom)
        (Y.toEnrichedFunctor.obj (c' ⊗ r))
  calc
    _ = (leftIndex d r).map c c' ≫
        (eHomWhiskerLeft V (r ⊗ c) (β_ r c').hom ≫
          Y.toEnrichedFunctor.map (r ⊗ c) (c' ⊗ r)) :=
      (Category.assoc _ _ _).trans (congrArg (fun q => (leftIndex d r).map c c' ≫ q) hp.symm)
    _ = (rightIndex d r).map c c' ≫
        (eHomWhiskerRight V (β_ r c).hom (c' ⊗ r) ≫
          Y.toEnrichedFunctor.map (r ⊗ c) (c' ⊗ r)) := by
      simpa only [Category.assoc] using congrArg
        (fun q => q ≫ Y.toEnrichedFunctor.map (r ⊗ c) (c' ⊗ r)) hi
    _ = _ := (congrArg (fun q => (rightIndex d r).map c c' ≫ q) hq).trans
      (Category.assoc _ _ _).symm

/-- Original left and right translations are isomorphic on every full enriched Hom. -/
def translationIso (b : EnrichedBraidedMonoidalCategoryData V I d)
    (Y : EnrichedFunctorCat V I) (r : I) :
    restrictionObject (leftIndex d r) Y ≅ restrictionObject (rightIndex d r) Y :=
  isoOfComponents _ _ (fun c => Y.toEnrichedFunctor.toOrdinaryFunctor.mapIso (β_ r c)) (by
    intro c c'
    have h := translatedBraid_whisker d b Y r c c'
    rw [MonoidalClosed.enrichedOrdinaryCategorySelf_eHomWhiskerLeft,
      MonoidalClosed.enrichedOrdinaryCategorySelf_eHomWhiskerRight] at h
    let F := (restrictionObject (leftIndex d r) Y).toEnrichedFunctor.map c c'
    let G := (restrictionObject (rightIndex d r) Y).toEnrichedFunctor.map c c'
    let q := Y.toEnrichedFunctor.toOrdinaryFunctor.map (β_ r c).hom
    let q' := Y.toEnrichedFunctor.toOrdinaryFunctor.map (β_ r c').hom
    have hu := congrArg MonoidalClosed.uncurry h
    have hp := MonoidalClosed.uncurry_pre_app (Y.toEnrichedFunctor.obj (c' ⊗ r)) G q
    have ht : q ▷ (c ⟶[V] c') = q ⊗ₘ 𝟙 (c ⟶[V] c') := (tensorHom_id q (c ⟶[V] c')).symm
    exact (MonoidalClosed.uncurry_natural_right F q').symm.trans
      (hu.trans (hp.trans (congrArg (fun p => p ≫ MonoidalClosed.uncurry G) ht))))


omit [HasColimitsOfSize.{uI, uI} V] [HasProducts.{uI} V] [HasEqualizers V] in
/-- Every forward block comparison is the original target index-braiding action. -/
theorem translationIso_hom_component (Y : EnrichedFunctorCat V I) (r c : I) :
    component (translationIso d b Y r).hom c =
      Y.toEnrichedFunctor.toOrdinaryFunctor.map (β_ r c).hom :=
  isoOfComponents_hom_component _ _ _ _ c

omit [HasColimitsOfSize.{uI, uI} V] [HasProducts.{uI} V] [HasEqualizers V] in
/-- Every inverse block comparison is the original inverse index-braiding action. -/
theorem translationIso_inv_component (Y : EnrichedFunctorCat V I) (r c : I) :
    component (translationIso d b Y r).inv c =
      Y.toEnrichedFunctor.toOrdinaryFunctor.map (β_ r c).inv :=
  isoOfComponents_inv_component _ _ _ _ c


omit [HasColimitsOfSize.{uI, uI} V] [HasProducts.{uI} V] [HasEqualizers V]
  [SymmetricCategory I] in
/-- Every original index map keeps the shifted unit coefficient and actual final-factor tensor. -/
theorem unitLabelPost (r n k : I) (f : n ⟶ k) :
    GenericRightTensor.label r n k (𝟙_ I) ((λ_ n).hom ≫ f) =
      (λ_ (n ⊗ r)).hom ≫ (f ▷ r) := by
  change (α_ (𝟙_ I) n r).inv ≫ (((λ_ n).hom ≫ f) ▷ r) = _
  rw [comp_whiskerRight, ← Category.assoc]
  exact congrArg (fun q => q ≫ (f ▷ r)) (GenericRightTensor.label_unit r n)

omit [HasProducts.{uI} V] [HasEqualizers V] [SymmetricCategory I] in
/-- The complete original enriched index Hom commutes with the full coend right shift. -/
theorem indexShift_full (hsep : IsSeparator (𝟙_ V))
    (d : EnrichedMonoidalCategoryData V I) (S : EnrichedFunctor V I V)
    (L : EnrichedFunctor.LaxMonoidalData d
      (MonoidalClosed.enrichedMonoidalCategoryDataSelf V) S) (r n k : I) :
    indexHom d S L n k ≫ GenericRightTensor.hom d S r n k =
      (fixedRightTensor d r).map n k ≫
        indexHom d S L (n ⊗ r) (k ⊗ r) := by
  apply hsep.def
  intro p
  obtain ⟨f, rfl⟩ := (eHomEquiv V).surjective p
  let eps := L.epsilon
  let h := coefficientHom d S n k (𝟙_ I) ((λ_ n).hom ≫ f)
  let t := GenericRightTensor.hom d S r n k
  let h' := coefficientHom d S (n ⊗ r) (k ⊗ r) (𝟙_ I)
    (GenericRightTensor.label r n k (𝟙_ I) ((λ_ n).hom ≫ f))
  have hs : h ≫ t = h' := by
    simpa only [h, t, h', coefficientHom, Category.assoc] using
      congrArg (fun q => (λ_ (S.obj (𝟙_ I))).inv ≫ q)
        (GenericRightTensor.hom_point_generator d S r n k (𝟙_ I) ((λ_ n).hom ≫ f))
  have h1 := indexHom_point_eq_coefficient d S L n k f
  have h2 := indexHom_point_eq_coefficient d S L (n ⊗ r) (k ⊗ r) (f ▷ r)
  have hl := congrArg (fun q => coefficientHom d S (n ⊗ r) (k ⊗ r) (𝟙_ I) q)
    (unitLabelPost r n k f)
  calc
    _ = (eps ≫ h) ≫ t :=
      (Category.assoc _ _ _).symm.trans (congrArg (fun q => q ≫ t) h1)
    _ = eps ≫ h' := (Category.assoc _ _ _).trans (congrArg (fun q => eps ≫ q) hs)
    _ = eps ≫ coefficientHom d S (n ⊗ r) (k ⊗ r) (𝟙_ I)
        ((λ_ (n ⊗ r)).hom ≫ (f ▷ r)) := congrArg (fun q => eps ≫ q) hl
    _ = eHomEquiv V (f ▷ r) ≫
        indexHom d S L (n ⊗ r) (k ⊗ r) := h2.symm
    _ = _ := (congrArg (fun q => q ≫
        indexHom d S L (n ⊗ r) (k ⊗ r))
      (fixedRightTensor_point d r f)).symm.trans (Category.assoc _ _ _)



omit [HasColimitsOfSize.{uI, uI} V] [HasProducts.{uI} V] [HasEqualizers V]
  [SymmetricCategory I] in
/-- The actual translated full Hom retains its original identity-weighted right tensor. -/
theorem translatedTarget_map_fixed (d : EnrichedMonoidalCategoryData V I)
    (Y : EnrichedFunctorCat V I) (r n k : I) :
    (EnrichedDayKernel.Closed.translatedTarget d Y r).toEnrichedFunctor.map n k =
      (fixedRightTensor d r).map n k ≫ Y.toEnrichedFunctor.map (n ⊗ r) (k ⊗ r) :=
  (Category.assoc _ _ _).symm

omit [HasProducts.{uI} V] [HasEqualizers V] [SymmetricCategory I] in
/-- The complete shifted restriction has exactly the original translated index Hom map. -/
theorem shiftedRestriction_map (hsep : IsSeparator (𝟙_ V))
    (d : EnrichedMonoidalCategoryData V I) (S : EnrichedFunctor V I V)
    (L : EnrichedFunctor.LaxMonoidalData d (MonoidalClosed.enrichedMonoidalCategoryDataSelf V) S)
    (F : EnrichedFunctorCat V (OperatorIndex d S L)) (r n k : I) :
    ((indexRestriction d S L).obj
      ((EnrichedFunctorCat.restriction (GenericRightTensor.indexShift d S L r)).obj
        F)).toEnrichedFunctor.map n k =
      (EnrichedDayKernel.Closed.translatedTarget d
        ((indexRestriction d S L).obj F) r).toEnrichedFunctor.map n k := by
  let H := F.toEnrichedFunctor.map (⟨n ⊗ r⟩ : OperatorIndex d S L) ⟨k ⊗ r⟩
  calc
    _ = indexHom d S L n k ≫ (GenericRightTensor.hom d S r n k ≫ H) := rfl
    _ = (fixedRightTensor d r).map n k ≫ (indexHom d S L (n ⊗ r) (k ⊗ r) ≫ H) :=
      (Category.assoc _ _ _).symm.trans
        ((congrArg (fun q => q ≫ H) (indexShift_full hsep d S L r n k)).trans
          (Category.assoc _ _ _))
    _ = (fixedRightTensor d r).map n k ≫ ((indexRestriction d S L).obj F).toEnrichedFunctor.map
        (n ⊗ r) (k ⊗ r) :=
      congrArg (fun q => (fixedRightTensor d r).map n k ≫ q)
        (indexRestriction_fullMap d S L F (n ⊗ r) (k ⊗ r)).symm
    _ = _ := (translatedTarget_map_fixed d ((indexRestriction d S L).obj F) r n k).symm

omit [HasProducts.{uI} V] [HasEqualizers V] in
/-- Original full-Hom compatibility gives the actual right-shift restriction isomorphism. -/
def shiftedRestrictionIso (hsep : IsSeparator (𝟙_ V))
    (d : EnrichedMonoidalCategoryData V I) (S : EnrichedFunctor V I V)
    (L : EnrichedFunctor.LaxMonoidalData d (MonoidalClosed.enrichedMonoidalCategoryDataSelf V) S)
    (F : EnrichedFunctorCat V (OperatorIndex d S L)) (r : I) :
    (indexRestriction d S L).obj
        ((EnrichedFunctorCat.restriction (GenericRightTensor.indexShift d S L r)).obj F) ≅
      EnrichedDayKernel.Closed.translatedTarget d ((indexRestriction d S L).obj F) r :=
  isoOfComponents _ _ (fun n => Iso.refl (F.toEnrichedFunctor.obj ⟨n ⊗ r⟩)) (by
    intro n k
    have h := congrArg MonoidalClosed.uncurry (shiftedRestriction_map hsep d S L F r n k)
    exact (Category.comp_id _).trans (h.trans
      ((congrArg (fun q => q ≫ MonoidalClosed.uncurry
        ((EnrichedDayKernel.Closed.translatedTarget d
          ((indexRestriction d S L).obj F) r).toEnrichedFunctor.map n k))
          (id_tensorHom_id _ _)).trans (Category.id_comp _)).symm))



omit [HasProducts.{uI} V] [HasEqualizers V] [SymmetricCategory I] in
/-- The forward shift-restriction comparison is the original identity on the original value. -/
theorem shiftedRestrictionIso_hom_component (hsep : IsSeparator (𝟙_ V))
    (F : EnrichedFunctorCat V (OperatorIndex d S L)) (r n : I) :
    component (shiftedRestrictionIso hsep d S L F r).hom n =
      𝟙 (F.toEnrichedFunctor.obj ⟨n ⊗ r⟩) :=
  isoOfComponents_hom_component _ _ _ _ n

omit [HasProducts.{uI} V] [HasEqualizers V] [SymmetricCategory I] in
/-- The inverse shift-restriction comparison retains the same entire original value. -/
theorem shiftedRestrictionIso_inv_component (hsep : IsSeparator (𝟙_ V))
    (F : EnrichedFunctorCat V (OperatorIndex d S L)) (r n : I) :
    component (shiftedRestrictionIso hsep d S L F r).inv n =
      𝟙 (F.toEnrichedFunctor.obj ⟨n ⊗ r⟩) :=
  isoOfComponents_inv_component _ _ _ _ n

/-- The actual full left translation and actual right slice use the original index braiding. -/
def translationTargetIso (d : EnrichedMonoidalCategoryData V I)
    (b : EnrichedBraidedMonoidalCategoryData V I d)
    (Y : EnrichedFunctorCat V I) (r : I) :
    parameterTarget d Y r ≅ Closed.translatedTarget d Y r :=
  translationIso d b Y r ≪≫ (eqToIso (Closed.translatedTarget_eq_restriction d Y r)).symm

/-- Original value, full block translation and an actual shift comparison give a cotensor ISO. -/
def rawRightShiftDiagramIso (r : I) (X : V) (N : Module d S L)
    (Z : EnrichedFunctorCat V I)
    (e : Z ≅ Closed.translatedTarget d (SphereModuleMappingEnd.diagram d S L N) r) :
    diagram d b S L (freeAt d S L r X) N ≅ cotensorObject X Z :=
  diagramIso d b S L r X N ≪≫
    (cotensor X).mapIso (translationTargetIso d b (SphereModuleMappingEnd.diagram d S L N) r) ≪≫
      (cotensor X).mapIso e.symm

universe uJ vJ

/-- The complete literal source and cotensor-restriction ISO in their original instance context. -/
def RightShiftRestrictionIsoType {J : Type uJ} [EnrichedCategory V J]
    (i : EnrichedFunctor V I J)
    (r : I) (X : V) (N : Module d S L) (F : EnrichedFunctorCat V J) :=
  diagram d b S L (freeAt d S L r X) N ≅ restrictionObject i (cotensorObject X F)

/-- The original cotensor restriction compares the same full source diagram with the
restriction of the actual cotensor. Both stages use one literal restriction carrier. -/
def rawRightShiftRestrictionIso {J : Type uJ} [EnrichedCategory V J]
    (i : EnrichedFunctor V I J)
    (r : I) (X : V) (N : Module d S L) (F : EnrichedFunctorCat V J)
    (e : restrictionObject i F ≅
      Closed.translatedTarget d (SphereModuleMappingEnd.diagram d S L N) r) :
    RightShiftRestrictionIsoType d b S L i r X N F :=
  rawRightShiftDiagramIso d b S L r X N (restrictionObject i F) e ≪≫
    cotensorRestrictionIso i X F

/-- Read the whole actual ISO back in its complete literal type. -/
def rightShiftRestrictionIsoReadback {J : Type uJ} [EnrichedCategory V J]
    (i : EnrichedFunctor V I J)
    (r : I) (X : V) (N : Module d S L) (F : EnrichedFunctorCat V J)
    (e : RightShiftRestrictionIsoType d b S L i r X N F) :
    diagram d b S L (freeAt d S L r X) N ≅ restrictionObject i (cotensorObject X F) := e



/-- Every actual target module arrow retains the literal source-ordered translated value. -/
theorem valueIso_target (r : I) (X : V) {N N' : Module d S L} (g : N ⟶ N') (c : I) :
    component (post d b S L (freeAt d S L r X) g) c ≫
        (valueIso d b S L r X N' c).hom =
      (valueIso d b S L r X N c).hom ≫
        (ihom X).map (component (SphereModuleMappingEnd.moduleMap d S L g) (r ⊗ c)) := by
  let q := component (SphereModuleMappingEnd.moduleMap d S L g) (r ⊗ c)
  let K := generatorMap d S L r X
  have hp := post_π d b S L (freeAt d S L r X) g c r
  have hn := (MonoidalClosed.pre K).naturality q
  calc
    _ = component (post d b S L (freeAt d S L r X) g) c ≫
        (π d b S L (freeAt d S L r X) N' c r ≫ (MonoidalClosed.pre K).app
          ((SphereModuleMappingEnd.diagram d S L N').toEnrichedFunctor.obj (r ⊗ c))) :=
      congrArg (fun t => component (post d b S L (freeAt d S L r X) g) c ≫ t)
        (valueIso_generator d b S L r X N' c)
    _ = π d b S L (freeAt d S L r X) N c r ≫
        ((ihom ((SphereModuleMappingEnd.diagram d S L
          (freeAt d S L r X)).toEnrichedFunctor.obj r)).map
          q ≫ (MonoidalClosed.pre K).app
            ((SphereModuleMappingEnd.diagram d S L N').toEnrichedFunctor.obj (r ⊗ c))) :=
      (Category.assoc _ _ _).symm.trans
        ((congrArg (fun t => t ≫ (MonoidalClosed.pre K).app
          ((SphereModuleMappingEnd.diagram d S L N').toEnrichedFunctor.obj (r ⊗ c))) hp).trans
            (Category.assoc _ _ _))
    _ = π d b S L (freeAt d S L r X) N c r ≫
        ((MonoidalClosed.pre K).app
          ((SphereModuleMappingEnd.diagram d S L N).toEnrichedFunctor.obj (r ⊗ c)) ≫
            (ihom X).map q) := congrArg (fun t => π d b S L (freeAt d S L r X) N c r ≫ t) hn
    _ = _ := (Category.assoc _ _ _).symm.trans
      (congrArg (fun t => t ≫ (ihom X).map q) (valueIso_generator d b S L r X N c).symm)

/-- The full original free-diagram arrow acts by the genuine free weighted-end transpose. -/
theorem valueIso_sourceMap (r s : I) (X Y : V)
    (f : Free.object s Y ⟶ Free.object r X) (N : Module d S L) (c : I) :
    component (pre d b S L (freeMap d S L f) N) c ≫
        (valueIso d b S L s Y N c).hom =
      (valueIso d b S L r X N c).hom ≫
        FreeWeightedEndMap.transpose r s X Y
          (Closed.translatedTarget d
            (SphereModuleMappingEnd.diagram d S L N) c).toEnrichedFunctor f :=
    by
  let Z := (Closed.translatedTarget d (SphereModuleMappingEnd.diagram d S L N) c).toEnrichedFunctor
  let R := (freeSourceValueIso d b S L (Free.object r X) N c).hom
  let T := (freeSourceValueIso d b S L (Free.object s Y) N c).hom
  let W := FreeWeightedEnd.forward r X Z
  let W' := FreeWeightedEnd.forward s Y Z
  let Q := FreeWeightedEndMap.transpose r s X Y Z f
  have hc := congrArg (fun t => component t c) (freeSource_sourceMap d b S L f N)
  rw [component_comp, component_comp] at hc
  have hw : component (Closed.pre d f (SphereModuleMappingEnd.diagram d S L N)) c ≫ W' = W ≫ Q :=
    (congrArg (fun t => t ≫ W')
      (ExternalTensorMappingEndAdjunction.sourceMap_component f
        (Closed.tensorRestriction d (SphereModuleMappingEnd.diagram d S L N)) c)).trans
      (FreeWeightedEndMap.precomp_forward r s X Y Z f)
  calc
    _ = component (pre d b S L (freeMap d S L f) N) c ≫ (T ≫ W') :=
      congrArg (fun t => component (pre d b S L (freeMap d S L f) N) c ≫ t)
        (valueIso_hom d b S L s Y N c)
    _ = R ≫ (component (Closed.pre d f (SphereModuleMappingEnd.diagram d S L N)) c ≫ W') :=
      (Category.assoc _ _ _).symm.trans
        ((congrArg (fun t => t ≫ W') hc).trans (Category.assoc _ _ _))
    _ = R ≫ (W ≫ Q) := congrArg (fun t => R ≫ t) hw
    _ = _ := (Category.assoc _ _ _).symm.trans
      (congrArg (fun t => t ≫ Q) (valueIso_hom d b S L r X N c).symm)



namespace Readback

/-- The literal original parameter evaluation equation, with one shared source type. -/
def ParameterApplyProperty (r : I) (X : V) (N : Module d S L) (c : I) {P : V}
    (f : P ⟶ value d b S L (freeAt d S L r X) N c) : Prop :=
  parameterEquiv d b S L r X N c P f =
    MonoidalClosed.uncurry (f ≫ (valueIso d b S L r X N c).hom)

/-- The actual original full parameter equation is proved before native specialization. -/
theorem parameter_apply (r : I) (X : V) (N : Module d S L) (c : I) {P : V}
    (f : P ⟶ value d b S L (freeAt d S L r X) N c) :
    ParameterApplyProperty d b S L r X N c f :=
  parameterEquiv_apply d b S L r X N c f

/-- The literal original parameter-map equation retains both entire source maps. -/
def ParameterRegradeProperty (r : I) (X : V) (N : Module d S L) (c : I)
    {P Q : V} (h : P ⟶ Q) (f : Q ⟶ value d b S L (freeAt d S L r X) N c) : Prop :=
  parameterEquiv d b S L r X N c P (h ≫ f) =
    (X ◁ h) ≫ parameterEquiv d b S L r X N c Q f

/-- Every complete original parameter map has its proved original coefficient tensoring. -/
theorem parameter_regrade (r : I) (X : V) (N : Module d S L) (c : I)
    {P Q : V} (h : P ⟶ Q) (f : Q ⟶ value d b S L (freeAt d S L r X) N c) :
    ParameterRegradeProperty d b S L r X N c h f :=
  parameterEquiv_regrade d b S L r X N c h f

/-- The literal full parameter-Hom equation retains every original source and target Hom. -/
def ValueParameterProperty (r : I) (X : V) (N : Module d S L) (c c' : I) : Prop :=
  parameterAction d b S L (freeAt d S L r X) N c c' ≫
      (valueIso d b S L r X N c').hom =
    ((valueIso d b S L r X N c).hom ⊗ₘ
      Closed.parameterComponent d (SphereModuleMappingEnd.diagram d S L N) c c' r) ≫
      eComp V X
        ((SphereModuleMappingEnd.diagram d S L N).toEnrichedFunctor.obj (r ⊗ c))
        ((SphereModuleMappingEnd.diagram d S L N).toEnrichedFunctor.obj (r ⊗ c'))

/-- The same original complete enriched parameter-Hom equation is actually proved. -/
theorem value_parameter (r : I) (X : V) (N : Module d S L) (c c' : I) :
    ValueParameterProperty d b S L r X N c c' := valueIso_parameter d b S L r X N c c'

/-- The literal target-arrow square retains the entire original module map at r tensor c. -/
def ValueTargetProperty (r : I) (X : V) {N N' : Module d S L} (g : N ⟶ N') (c : I) : Prop :=
  component (post d b S L (freeAt d S L r X) g) c ≫
      (valueIso d b S L r X N' c).hom =
    (valueIso d b S L r X N c).hom ≫
      (ihom X).map (component (SphereModuleMappingEnd.moduleMap d S L g) (r ⊗ c))

/-- Every original target-arrow square uses its proved full coefficient map. -/
theorem value_target (r : I) (X : V) {N N' : Module d S L} (g : N ⟶ N') (c : I) :
    ValueTargetProperty d b S L r X g c := valueIso_target d b S L r X g c

/-- The literal source-arrow square retains the original free weighted-end transpose. -/
def ValueSourceMapProperty (r s : I) (X Y : V)
    (f : Free.object s Y ⟶ Free.object r X) (N : Module d S L) (c : I) : Prop :=
  component (pre d b S L (freeMap d S L f) N) c ≫
      (valueIso d b S L s Y N c).hom =
    (valueIso d b S L r X N c).hom ≫
      FreeWeightedEndMap.transpose r s X Y
        (Closed.translatedTarget d (SphereModuleMappingEnd.diagram d S L N) c).toEnrichedFunctor f

/-- Every full original free source arrow has its actually proved transpose square. -/
theorem value_sourceMap (r s : I) (X Y : V)
    (f : Free.object s Y ⟶ Free.object r X) (N : Module d S L) (c : I) :
    ValueSourceMapProperty d b S L r s X Y f N c := valueIso_sourceMap d b S L r s X Y f N c

end Readback

end CategoryTheory.Enriched.ModuleMappingR.FreeEvaluation
