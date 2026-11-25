/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.CategoryTheory.Enriched.Monoidal.DayConvolution.Closed
public import MathlibExt.CategoryTheory.Enriched.Monoidal.DayConvolution.BraidingMonoidal
public import MathlibExt.CategoryTheory.Enriched.Monoidal.DayConvolution.LaxMonoidCommutativity
public import MathlibExt.CategoryTheory.Enriched.SphereModuleMappingEnd
public import MathlibExt.CategoryTheory.Enriched.PointwiseShapeInstances
public import MathlibExt.CategoryTheory.Monoidal.RightModuleMappingEnd

/-!
# Mapping_R on actual right Day modules

The source mapping diagram is the equalizer of the two complete Day
internal-Hom action arrows. Its value at `c` is an equalizer on the genuine
weighted end with projections `[M(j), N(j ⊗ c)]`. The parameter action is
the full enriched action of this diagram. All compatible base-object families
retain genuine enriched naturality, and the balancing criterion tests every
original Day generator, with its whole output weight and both source indices.

The raw construction does not assume that the coefficient monoid is
commutative. Only the final module-valued and balanced adjunction section
uses its original braided lax-monoidal law.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

universe uV vV uI vI

open CategoryTheory Limits MonoidalCategory BraidedCategory
open scoped MonoidalClosed CategoryTheory.MonObj

namespace CategoryTheory.Enriched.ModuleMappingR

open EnrichedFunctorCat EnrichedDayKernel

attribute [local instance] Enriched.prodCategory ColimitMonoidal.smallestColimits
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

/-- The original complete stock right modules over the constructed sphere Day monoid. -/
abbrev Module := SphereModuleMappingEnd.Module d S L

/-- The original source right-action domain is the actual selected Day tensor. -/
abbrev sourceTensor (M : Module d S L) : EnrichedFunctorCat V I :=
  Closed.tensorObject d (SphereModuleMappingEnd.diagram d S L M) ⟨S⟩

/-- The actual ambient mapping diagram uses the full right-translation weighted end. -/
abbrev ambient (M N : Module d S L) : EnrichedFunctorCat V I :=
  Closed.rightObject d (SphereModuleMappingEnd.diagram d S L M)
    (SphereModuleMappingEnd.diagram d S L N)

/-- The complete target of both source action arrows, with no dropped Day generators. -/
abbrev actionTarget (M N : Module d S L) : EnrichedFunctorCat V I :=
  Closed.rightObject d (sourceTensor d S L M) (SphereModuleMappingEnd.diagram d S L N)

/-- The whole original source right action induces literal Day internal-Hom precomposition. -/
def sourceActionMap (M N : Module d S L) : ambient d S L M N ⟶ actionTarget d S L M N := by
  letI : MonoidalCategory (EnrichedFunctorCat V I) := ColimitMonoidal.monoidalCategory d
  letI : SymmetricCategory (EnrichedFunctorCat V I) := BraidingMonoidal.symmetricCategory d b
  letI : MonoidalClosed (EnrichedFunctorCat V I) := Closed.monoidalClosed d
  letI : MonObj (⟨S⟩ : EnrichedFunctorCat V I) := LaxMonoid.monObj d S L
  exact RightModuleMappingEnd.sourceActionMap (⟨S⟩ : EnrichedFunctorCat V I) M N

/-- The whole original target right action induces the literal source evaluation transpose. -/
def targetActionMap (M N : Module d S L) : ambient d S L M N ⟶ actionTarget d S L M N := by
  letI : MonoidalCategory (EnrichedFunctorCat V I) := ColimitMonoidal.monoidalCategory d
  letI : SymmetricCategory (EnrichedFunctorCat V I) := BraidingMonoidal.symmetricCategory d b
  letI : MonoidalClosed (EnrichedFunctorCat V I) := Closed.monoidalClosed d
  letI : MonObj (⟨S⟩ : EnrichedFunctorCat V I) := LaxMonoid.monObj d S L
  exact RightModuleMappingEnd.targetActionMap (⟨S⟩ : EnrichedFunctorCat V I) M N

/-- The actual source Mapping_R diagram is the full equalizer of the original action arrows. -/
def diagram (M N : Module d S L) : EnrichedFunctorCat V I :=
  equalizer (sourceActionMap d S L M N) (targetActionMap d b S L M N)

/-- Its genuine enriched inclusion retains the full original ambient end diagram. -/
def ι (M N : Module d S L) : diagram d b S L M N ⟶ ambient d S L M N :=
  equalizer.ι (sourceActionMap d S L M N) (targetActionMap d b S L M N)

/-- The complete source action diagram commutes after the original equalizer inclusion. -/
@[reassoc]
theorem condition (M N : Module d S L) :
    ι d b S L M N ≫ sourceActionMap d S L M N =
      ι d b S L M N ≫ targetActionMap d b S L M N := equalizer.condition _ _

/-- Every original parameter object selects its actual Mapping_R value. -/
abbrev value (M N : Module d S L) (c : I) : V :=
  (diagram d b S L M N).toEnrichedFunctor.obj c

/-- The full evaluated equalizer inclusion at the original parameter. -/
abbrev valueι (M N : Module d S L) (c : I) :
    value d b S L M N c ⟶
      Closed.object d (SphereModuleMappingEnd.diagram d S L M)
        (SphereModuleMappingEnd.diagram d S L N) c :=
  component (ι d b S L M N) c

/-- Every original source object supplies its whole right-translation internal-Hom projection. -/
def π (M N : Module d S L) (c j : I) : value d b S L M N c ⟶
    (ihom ((SphereModuleMappingEnd.diagram d S L M).toEnrichedFunctor.obj j)).obj
      ((SphereModuleMappingEnd.diagram d S L N).toEnrichedFunctor.obj (j ⊗ c)) :=
  valueι d b S L M N c ≫
    Closed.π d (SphereModuleMappingEnd.diagram d S L M)
      (SphereModuleMappingEnd.diagram d S L N) c j

/-- The actual evaluated source action fork keeps the unchanged parameter value. -/
def valueFork (M N : Module d S L) (c : I) :
    Fork (component (sourceActionMap d S L M N) c)
      (component (targetActionMap d b S L M N) c) :=
  Fork.ofι (valueι d b S L M N c)
    (by
      have h := congrArg (fun t => component t c) (condition d b S L M N)
      simpa only [component_comp] using h)

/-- Genuine evaluation preserves the original entire Mapping_R action equalizer. -/
def valueForkIsLimit (M N : Module d S L) (c : I) :
    IsLimit (valueFork d b S L M N c) := by
  have h := isLimitForkMapOfIsLimit (G := EnrichedFunctorCat.evaluation (V := V) c)
    (condition d b S L M N)
    (equalizerIsEqualizer (sourceActionMap d S L M N) (targetActionMap d b S L M N))
  exact h

/-- Every whole original mapping value is determined by its genuine right-translation
component projections. -/
@[ext]
theorem hom_ext (M N : Module d S L) (c : I) {P : V}
    {f g : P ⟶ value d b S L M N c}
    (h : ∀ j, f ≫ π d b S L M N c j = g ≫ π d b S L M N c j) : f = g := by
  apply Fork.IsLimit.hom_ext (valueForkIsLimit d b S L M N c)
  change f ≫ valueι d b S L M N c = g ≫ valueι d b S L M N c
  apply Closed.hom_ext d (SphereModuleMappingEnd.diagram d S L M)
    (SphereModuleMappingEnd.diagram d S L N) c
  intro j
  simpa only [π, Category.assoc] using h j

/-- The full original parameter Hom action, before choosing any parameter point. -/
abbrev parameterAction (M N : Module d S L) (c c' : I) :
    value d b S L M N c ⊗ (c ⟶[V] c') ⟶ value d b S L M N c' :=
  MonoidalClosed.uncurry ((diagram d b S L M N).toEnrichedFunctor.map c c')

/-- The actual ambient equalizer inclusion intertwines the whole enriched parameter action. -/
@[reassoc]
theorem parameterAction_valueι (M N : Module d S L) (c c' : I) :
    parameterAction d b S L M N c c' ≫ valueι d b S L M N c' =
      (valueι d b S L M N c ⊗ₘ 𝟙 (c ⟶[V] c')) ≫
        MonoidalClosed.uncurry ((ambient d S L M N).toEnrichedFunctor.map c c') :=
  (ι d b S L M N).uncurriedNaturality c c'

/-- Every original component of the whole parameter action is composition with the literal
right-tensor parameter Hom map. -/
@[reassoc]
theorem parameterAction_π (M N : Module d S L) (c c' j : I) :
    parameterAction d b S L M N c c' ≫ π d b S L M N c' j =
      (π d b S L M N c j ⊗ₘ
        Closed.parameterComponent d (SphereModuleMappingEnd.diagram d S L N) c c' j) ≫
        eComp V ((SphereModuleMappingEnd.diagram d S L M).toEnrichedFunctor.obj j)
          ((SphereModuleMappingEnd.diagram d S L N).toEnrichedFunctor.obj (j ⊗ c))
          ((SphereModuleMappingEnd.diagram d S L N).toEnrichedFunctor.obj (j ⊗ c')) := by
  rw [π, ← Category.assoc, parameterAction_valueι, Category.assoc, Closed.rightObject_map_π]
  simp only [tensorHom_comp_tensorHom_assoc, Category.id_comp, π]

/-- All full parameter families are genuine enriched transformations to the original right
translation, subject to the whole source action equalizer. -/
@[ext]
structure Family (M N : Module d S L) (c : I) (P : V) where
  /-- The complete central-graded transformation to the right translated target. -/
  transformation : GradedNatTrans ((Center.ofBraided V).obj P)
    (SphereModuleMappingEnd.diagram d S L M).toEnrichedFunctor
    (Closed.translatedTarget d (SphereModuleMappingEnd.diagram d S L N) c).toEnrichedFunctor
  condition :
    GradingConvention.endFromPositive (SphereModuleMappingEnd.diagram d S L M).toEnrichedFunctor
      (Closed.translatedTarget d (SphereModuleMappingEnd.diagram d S L N) c).toEnrichedFunctor
      transformation ≫ component (sourceActionMap d S L M N) c =
    GradingConvention.endFromPositive (SphereModuleMappingEnd.diagram d S L M).toEnrichedFunctor
      (Closed.translatedTarget d (SphereModuleMappingEnd.diagram d S L N) c).toEnrichedFunctor
      transformation ≫ component (targetActionMap d b S L M N) c
/-- A map into the actual Mapping_R value gives its full original compatible family. -/
def toFamily (M N : Module d S L) (c : I) {P : V}
    (f : P ⟶ value d b S L M N c) : Family d b S L M N c P where
  transformation := GradingConvention.endToPositive
    (SphereModuleMappingEnd.diagram d S L M).toEnrichedFunctor
    (Closed.translatedTarget d (SphereModuleMappingEnd.diagram d S L N) c).toEnrichedFunctor
    (f ≫ valueι d b S L M N c)
  condition := by
    rw [GradingConvention.endFromPositive_toPositive]
    have h := (valueFork d b S L M N c).condition
    change valueι d b S L M N c ≫ component (sourceActionMap d S L M N) c =
      valueι d b S L M N c ≫ component (targetActionMap d b S L M N) c at h
    simpa only [Category.assoc] using congrArg (fun z => f ≫ z) h

/-- Every full original compatible family lifts through the evaluated source action fork. -/
def lift (M N : Module d S L) (c : I) {P : V}
    (q : Family d b S L M N c P) : P ⟶ value d b S L M N c :=
  Fork.IsLimit.lift (valueForkIsLimit d b S L M N c)
    (GradingConvention.endFromPositive (SphereModuleMappingEnd.diagram d S L M).toEnrichedFunctor
      (Closed.translatedTarget d (SphereModuleMappingEnd.diagram d S L N) c).toEnrichedFunctor
      q.transformation) q.condition

/-- Every whole original compatible family is retained by the lift into the ambient end. -/
@[reassoc]
theorem lift_valueι (M N : Module d S L) (c : I) {P : V}
    (q : Family d b S L M N c P) :
    lift d b S L M N c q ≫ valueι d b S L M N c =
      GradingConvention.endFromPositive (SphereModuleMappingEnd.diagram d S L M).toEnrichedFunctor
        (Closed.translatedTarget d (SphereModuleMappingEnd.diagram d S L N) c).toEnrichedFunctor
        q.transformation := Fork.IsLimit.lift_ι' _ _ _

/-- Every entire original component is retained by the Mapping_R value lift. -/
@[reassoc]
theorem lift_π (M N : Module d S L) (c : I) {P : V}
    (q : Family d b S L M N c P) (j : I) :
    lift d b S L M N c q ≫ π d b S L M N c j = q.transformation.app j := by
  rw [π, ← Category.assoc, lift_valueι]
  exact GradingConvention.endFromPositive_symmetric_π _ _ _ j

/-- Every represented complete family has its original right-translation component map. -/
theorem toFamily_app (M N : Module d S L) (c : I) {P : V}
    (f : P ⟶ value d b S L M N c) (j : I) :
    (toFamily d b S L M N c f).transformation.app j = f ≫ π d b S L M N c j := by
  rw [toFamily, GradingConvention.endToPositive_app_symmetric]
  exact Category.assoc _ _ _

/-- Lifting and recovering retains the entire genuine compatible family. -/
theorem toFamily_lift (M N : Module d S L) (c : I) {P : V}
    (q : Family d b S L M N c P) :
    toFamily d b S L M N c (lift d b S L M N c q) = q := by
  apply Family.ext
  apply GradedNatTrans.ext
  funext j
  rw [toFamily_app, lift_π]

/-- Taking a compatible family and lifting recovers every entire original Mapping_R map. -/
theorem lift_toFamily (M N : Module d S L) (c : I) {P : V}
    (f : P ⟶ value d b S L M N c) : lift d b S L M N c (toFamily d b S L M N c f) = f := by
  apply hom_ext d b S L M N c
  intro j
  rw [lift_π, toFamily_app]

/-- The whole Mapping_R value represents all full compatible V-parameterized transformations. -/
def parameterEquiv (M N : Module d S L) (c : I) (P : V) :
    (P ⟶ value d b S L M N c) ≃ Family d b S L M N c P where
  toFun := toFamily d b S L M N c
  invFun := lift d b S L M N c
  left_inv := lift_toFamily d b S L M N c
  right_inv := toFamily_lift d b S L M N c

/-- The source translated action keeps the literal index block swap. -/
def translationSwap (j a c : I) : (j ⊗ c) ⊗ a ⟶ (j ⊗ a) ⊗ c :=
  (α_ j c a).hom ≫ (j ◁ (β_ c a).hom) ≫ (α_ j a c).inv

/-- The actual right action on the translated target keeps the original right action and the
entire index block swap. -/
def translatedAction (N : Module d S L) (c j a : I) :
    (SphereModuleMappingEnd.diagram d S L N).toEnrichedFunctor.obj (j ⊗ c) ⊗ S.obj a ⟶
      (SphereModuleMappingEnd.diagram d S L N).toEnrichedFunctor.obj ((j ⊗ a) ⊗ c) :=
  ExternalRightModule.sigma d S (SphereModuleMappingEnd.diagram d S L N)
      (SphereModuleMappingEnd.action d S L N) (j ⊗ c) a ≫
    (SphereModuleMappingEnd.diagram d S L N).toEnrichedFunctor.toOrdinaryFunctor.map
      (translationSwap j a c)

end CategoryTheory.Enriched.ModuleMappingR
