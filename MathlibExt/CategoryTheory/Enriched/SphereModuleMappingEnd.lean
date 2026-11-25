/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.CategoryTheory.Enriched.GradingConvention
public import MathlibExt.CategoryTheory.Enriched.WeightedEndVariance
public import MathlibExt.CategoryTheory.Enriched.MappingCompositionAlgebra
public import MathlibExt.CategoryTheory.Enriched.Monoidal.DayConvolution.ExternalRightModuleCorrespondence

/-!
# The enriched mapping end of stock right Day modules

The mapping object is the equalizer of the two complete action maps out of the
actual enriched mapping end of the underlying diagrams. One map precomposes
with the source action; the other tensors each component with the sphere
coefficient and postcomposes with the target action. Every pair of index
objects is retained, together with the full enriched naturality already
represented by the ambient end.

This is the enrichment-base mapping-object form of the module action
equalizer in Mandell--May--Schwede--Shipley, *Model categories of diagram
spectra*, equation (22.3), using the external actions of Definition 1.9.
The product over index pairs is its complete component presentation.

The construction uses the genuine stock modules for the constructed Day
convolution. It requires only limits in the enrichment base, its original
closed structure, and the colimits used by Day convolution.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 512
set_option backward.isDefEq.respectTransparency false

noncomputable section

universe uV vV uI vI

open CategoryTheory CategoryTheory.Limits MonoidalCategory BraidedCategory
open scoped MonoidalClosed CategoryTheory.MonObj

namespace CategoryTheory.Enriched.SphereModuleMappingEnd

open EnrichedFunctorCat EnrichedDayKernel

attribute [local instance] ColimitMonoidal.smallestColimits
attribute [local instance] MonoidalLeftAction.monoidalOppositeLeftAction

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [SymmetricCategory V] [MonoidalClosed V]
  {I : Type uI} [Category.{vI} I] [MonoidalCategory I]
  [EnrichedOrdinaryCategory V I] [HasColimitsOfSize.{uI, uI} V]
  [HasProducts.{uI} V] [HasEqualizers V]
  (d : EnrichedMonoidalCategoryData V I) (S : EnrichedFunctor V I V)
  (L : EnrichedFunctor.LaxMonoidalData d (MonoidalClosed.enrichedMonoidalCategoryDataSelf V) S)

/-- The original stock right modules for the constructed Day monoidal category. -/
abbrev Module :=
  letI := ColimitMonoidal.monoidalCategory d
  letI := LaxMonoid.monObj d S L
  CommutativeModuleConversion.RightModule (⟨S⟩ : EnrichedFunctorCat V I)
/-- The stock module category under the explicitly constructed Day and monoid instances. -/
local instance moduleCategory : Category (Module d S L) := by
  letI := ColimitMonoidal.monoidalCategory d
  letI := LaxMonoid.monObj d S L
  infer_instance

/-- The unchanged underlying genuine enriched diagram of the stock module. -/
def diagram (M : Module d S L) : EnrichedFunctorCat V I := by
  letI := ColimitMonoidal.monoidalCategory d
  letI := LaxMonoid.monObj d S L
  exact M.X

/-- The unchanged stock action under its explicitly constructed Day instances. -/
def action (M : Module d S L) : ExternalRightModule.Action d S (diagram d S L M) := by
  letI := ColimitMonoidal.monoidalCategory d
  letI := LaxMonoid.monObj d S L
  exact M.action

/-- The complete original genuine transformation of a stock module morphism. -/
def moduleMap {M N : Module d S L} (f : M ⟶ N) : diagram d S L M ⟶ diagram d S L N := by
  letI := ColimitMonoidal.monoidalCategory d
  letI := LaxMonoid.monObj d S L
  exact f.hom

omit [HasProducts.{uI} V] [HasEqualizers V] in
/-- The underlying genuine transformation determines the whole stock module morphism. -/
theorem moduleMap_ext {M N : Module d S L} {f g : M ⟶ N}
    (h : moduleMap d S L f = moduleMap d S L g) : f = g := by
  let : MonoidalCategory (EnrichedFunctorCat V I) := ColimitMonoidal.monoidalCategory d
  let : MonObj (⟨S⟩ : EnrichedFunctorCat V I) := LaxMonoid.monObj d S L
  exact Mod.Hom.ext h

omit [HasProducts.{uI} V] [HasEqualizers V] in
/-- Forgetting the stock identity retains the original whole diagram identity. -/
@[simp]
theorem moduleMap_id (M : Module d S L) : moduleMap d S L (𝟙 M) = 𝟙 (diagram d S L M) := rfl

omit [HasProducts.{uI} V] [HasEqualizers V] in
/-- Forgetting stock composition retains both complete original diagram transformations. -/
@[simp]
theorem moduleMap_comp {J M N : Module d S L} (f : J ⟶ M) (g : M ⟶ N) :
    moduleMap d S L (f ≫ g) = moduleMap d S L f ≫ moduleMap d S L g := rfl

variable (M N : Module d S L)

/-- The actual enriched mapping end of the two underlying genuine diagrams. -/
abbrev ambientHom : V := WeightedEndVariance.object (diagram d S L M) (diagram d S L N)

/-- The full internal Hom containing the action square at a pair of index objects. -/
abbrev actionObjects (p : I × I) : V :=
  (ihom ((diagram d S L M).toEnrichedFunctor.obj p.1 ⊗ S.obj p.2)).obj
    ((diagram d S L N).toEnrichedFunctor.obj (p.1 ⊗ p.2))

/-- Precomposition with the literal stock source action. -/
def sourceActionMap : ambientHom d S L M N ⟶ ∏ᶜ actionObjects d S L M N :=
  Pi.lift fun p =>
    WeightedEndVariance.projection (diagram d S L M) (diagram d S L N) (p.1 ⊗ p.2) ≫
      eHomWhiskerRight V
        (ExternalRightModule.sigma d S (diagram d S L M) (action d S L M) p.1 p.2)
        ((diagram d S L N).toEnrichedFunctor.obj (p.1 ⊗ p.2))

/-- Tensoring with the whole coefficient followed by the literal stock target action. -/
def targetActionMap : ambientHom d S L M N ⟶ ∏ᶜ actionObjects d S L M N :=
  Pi.lift fun p =>
    WeightedEndVariance.projection (diagram d S L M) (diagram d S L N) p.1 ≫
      (SphereOperator.fixedRightTensor
        (MonoidalClosed.enrichedMonoidalCategoryDataSelf V) (S.obj p.2)).map
        ((diagram d S L M).toEnrichedFunctor.obj p.1) ((diagram d S L N).toEnrichedFunctor.obj
          p.1) ≫
      eHomWhiskerLeft V ((diagram d S L M).toEnrichedFunctor.obj p.1 ⊗ S.obj p.2)
        (ExternalRightModule.sigma d S (diagram d S L N) (action d S L N) p.1 p.2)

/-- Every full source-action component is the actual internal-Hom precomposition map. -/
@[reassoc]
theorem sourceActionMap_π (n a : I) :
    sourceActionMap d S L M N ≫ Pi.π (actionObjects d S L M N) (n, a) =
      WeightedEndVariance.projection (diagram d S L M) (diagram d S L N) (n ⊗ a) ≫
        eHomWhiskerRight V
          (ExternalRightModule.sigma d S (diagram d S L M) (action d S L M) n a)
          ((diagram d S L N).toEnrichedFunctor.obj (n ⊗ a)) :=
  Pi.lift_comp_π _ (n, a)

/-- Every full target-action component retains tensoring and the original target action. -/
@[reassoc]
theorem targetActionMap_π (n a : I) :
    targetActionMap d S L M N ≫ Pi.π (actionObjects d S L M N) (n, a) =
      WeightedEndVariance.projection (diagram d S L M) (diagram d S L N) n ≫
        (SphereOperator.fixedRightTensor
          (MonoidalClosed.enrichedMonoidalCategoryDataSelf V) (S.obj a)).map
          ((diagram d S L M).toEnrichedFunctor.obj n) ((diagram d S L N).toEnrichedFunctor.obj n) ≫
        eHomWhiskerLeft V ((diagram d S L M).toEnrichedFunctor.obj n ⊗ S.obj a)
          (ExternalRightModule.sigma d S (diagram d S L N) (action d S L N) n a) :=
  Pi.lift_comp_π _ (n, a)

/-- The enriched module mapping object is the actual equalizer of both full action maps. -/
def Hom : V := equalizer (sourceActionMap d S L M N) (targetActionMap d S L M N)

/-- Its original forgetful map lands in the actual ambient enriched end. -/
def ι : Hom d S L M N ⟶ ambientHom d S L M N :=
  equalizer.ι (sourceActionMap d S L M N) (targetActionMap d S L M N)

/-- Every full component is the original ambient-end projection after the equalizer inclusion. -/
def π (n : I) : Hom d S L M N ⟶
    (ihom ((diagram d S L M).toEnrichedFunctor.obj n)).obj ((diagram d S L
      N).toEnrichedFunctor.obj n) :=
  ι d S L M N ≫ WeightedEndVariance.projection (diagram d S L M) (diagram d S L N) n

/-- The chosen object has literally the MMSS equalizer presentation. -/
theorem Hom_eq : Hom d S L M N =
    equalizer (sourceActionMap d S L M N) (targetActionMap d S L M N) := rfl

/-- Both complete action arrows agree after the original equalizer inclusion. -/
@[reassoc]
theorem condition : ι d S L M N ≫ sourceActionMap d S L M N =
    ι d S L M N ≫ targetActionMap d S L M N :=
  equalizer.condition _ _

/-- The actual fork of the two whole action arrows. -/
def fork : Fork (sourceActionMap d S L M N) (targetActionMap d S L M N) :=
  Fork.ofι (ι d S L M N) (condition d S L M N)

/-- The constructed mapping end is the limit of that actual full action fork. -/
def forkIsLimit : IsLimit (fork d S L M N) :=
  equalizerIsEqualizer (sourceActionMap d S L M N) (targetActionMap d S L M N)

/-- Every whole source-action square agrees with its whole target-action square. -/
theorem action_condition (n a : I) :
    π d S L M N (n ⊗ a) ≫
        eHomWhiskerRight V
          (ExternalRightModule.sigma d S (diagram d S L M) (action d S L M) n a)
          ((diagram d S L N).toEnrichedFunctor.obj (n ⊗ a)) =
      π d S L M N n ≫
        (SphereOperator.fixedRightTensor
          (MonoidalClosed.enrichedMonoidalCategoryDataSelf V) (S.obj a)).map
          ((diagram d S L M).toEnrichedFunctor.obj n) ((diagram d S L N).toEnrichedFunctor.obj n) ≫
        eHomWhiskerLeft V ((diagram d S L M).toEnrichedFunctor.obj n ⊗ S.obj a)
          (ExternalRightModule.sigma d S (diagram d S L N) (action d S L N) n a) := by
  have h := congrArg (fun f => f ≫ Pi.π (actionObjects d S L M N) (n, a))
    (condition d S L M N)
  simpa only [Category.assoc, sourceActionMap_π, targetActionMap_π, π] using h

/-- All original component projections determine every map into the actual module end. -/
@[ext]
theorem hom_ext {P : V} {f g : P ⟶ Hom d S L M N}
    (h : ∀ n, f ≫ π d S L M N n = g ≫ π d S L M N n) : f = g := by
  apply equalizer.hom_ext
  apply weightedEnd.hom_ext (diagram d S L M).toEnrichedFunctor (diagram d S L N).toEnrichedFunctor
  intro n
  exact (Category.assoc f (ι d S L M N)
    (WeightedEndVariance.projection (diagram d S L M) (diagram d S L N) n)).trans
      ((h n).trans (Category.assoc g (ι d S L M N)
        (WeightedEndVariance.projection (diagram d S L M) (diagram d S L N) n)).symm)

/-- Complete genuine enriched transformations preserving every coefficient-action map. -/
@[ext]
structure Family (P : V) where
  /-- The entire enriched transformation at the original parameter object. -/
  transformation : GradedNatTrans ((Center.ofBraided V).obj P)
    (diagram d S L M).toEnrichedFunctor (diagram d S L N).toEnrichedFunctor
  /-- Compatibility is equality of the two whole source/target internal-Hom maps. -/
  action_condition : ∀ n a,
    transformation.app (n ⊗ a) ≫
        eHomWhiskerRight V
          (ExternalRightModule.sigma d S (diagram d S L M) (action d S L M) n a)
          ((diagram d S L N).toEnrichedFunctor.obj (n ⊗ a)) =
      transformation.app n ≫
        (SphereOperator.fixedRightTensor
          (MonoidalClosed.enrichedMonoidalCategoryDataSelf V) (S.obj a)).map
          ((diagram d S L M).toEnrichedFunctor.obj n) ((diagram d S L N).toEnrichedFunctor.obj n) ≫
        eHomWhiskerLeft V ((diagram d S L M).toEnrichedFunctor.obj n ⊗ S.obj a)
          (ExternalRightModule.sigma d S (diagram d S L N) (action d S L N) n a)

/-- Every arrow into the original equalizer gives its full genuine compatible family. -/
def toFamily {P : V} (f : P ⟶ Hom d S L M N) : Family d S L M N P where
  transformation := GradingConvention.endToPositive (diagram d S L M).toEnrichedFunctor (diagram
    d S L N).toEnrichedFunctor
    (f ≫ ι d S L M N)
  action_condition n a := by
    simp only [GradingConvention.endToPositive_app_symmetric]
    simpa only [π, WeightedEndVariance.projection, Category.assoc] using congrArg (fun g => f ≫ g)
      (action_condition d S L M N n a)

/-- The full represented family retains each original mapping-end projection. -/
theorem toFamily_app {P : V} (f : P ⟶ Hom d S L M N) (n : I) :
    (toFamily d S L M N f).transformation.app n = f ≫ π d S L M N n := by
  dsimp only [toFamily]
  rw [GradingConvention.endToPositive_app_symmetric]
  exact Category.assoc _ _ _

/-- A complete compatible enriched family lifts through the actual equalizer. -/
def lift {P : V} (q : Family d S L M N P) : P ⟶ Hom d S L M N :=
  equalizer.lift
    (GradingConvention.endFromPositive (diagram d S L M).toEnrichedFunctor (diagram d S L
      N).toEnrichedFunctor q.transformation)
    (by
      apply Pi.hom_ext
      rintro ⟨n, a⟩
      simp only [Category.assoc, sourceActionMap_π, targetActionMap_π,
        ← Category.assoc _ (WeightedEndVariance.projection (diagram d S L M) (diagram d S L N) _),
        GradingConvention.endFromPositive_symmetric_π]
      exact q.action_condition n a)

/-- The full lift has exactly its original map to the ambient enriched end. -/
@[reassoc]
theorem lift_ι {P : V} (q : Family d S L M N P) :
    lift d S L M N q ≫ ι d S L M N =
      GradingConvention.endFromPositive (diagram d S L M).toEnrichedFunctor (diagram d S L
        N).toEnrichedFunctor q.transformation :=
  equalizer.lift_ι _ _

/-- The full lift retains every original parameter component. -/
@[reassoc]
theorem lift_π {P : V} (q : Family d S L M N P) (n : I) :
    lift d S L M N q ≫ π d S L M N n = q.transformation.app n := by
  rw [π, ← Category.assoc, lift_ι]
  exact GradingConvention.endFromPositive_symmetric_π _ _ _ n

/-- Recovering and lifting a complete represented family recovers the original map. -/
theorem lift_toFamily {P : V} (f : P ⟶ Hom d S L M N) :
    lift d S L M N (toFamily d S L M N f) = f := by
  apply hom_ext d S L M N
  intro n
  rw [lift_π, toFamily_app]

/-- Lifting and recovering a complete genuine family recovers that whole family. -/
theorem toFamily_lift {P : V} (q : Family d S L M N P) :
    toFamily d S L M N (lift d S L M N q) = q := by
  apply Family.ext
  apply GradedNatTrans.ext
  funext n
  rw [toFamily_app, lift_π]

/-- The actual equalizer represents every full compatible enriched parameter family. -/
def parameterEquiv (P : V) : (P ⟶ Hom d S L M N) ≃ Family d S L M N P where
  toFun := toFamily d S L M N
  invFun := lift d S L M N
  left_inv := lift_toFamily d S L M N
  right_inv := toFamily_lift d S L M N

/-- The component characteristic uniquely specifies every lift of a complete family. -/
theorem lift_unique {P : V} (q : Family d S L M N P) (f : P ⟶ Hom d S L M N)
    (h : ∀ n, f ≫ π d S L M N n = q.transformation.app n) :
    f = lift d S L M N q := by
  apply hom_ext d S L M N
  intro n
  rw [lift_π]
  exact h n

/-- The original pointed/enriched evaluation on every whole underlying diagram object. -/
def evaluation (n : I) : (diagram d S L M).toEnrichedFunctor.obj n ⊗ Hom d S L M N ⟶
    (diagram d S L N).toEnrichedFunctor.obj n :=
  MonoidalClosed.uncurry (π d S L M N n)

/-- Every lifted full parameter family evaluates by its given original component. -/
@[reassoc]
theorem lift_evaluation {P : V} (q : Family d S L M N P) (n : I) :
    ((diagram d S L M).toEnrichedFunctor.obj n ◁ lift d S L M N q) ≫ evaluation d S L M N n =
      MonoidalClosed.uncurry (q.transformation.app n) := by
  rw [evaluation, ← MonoidalClosed.uncurry_natural_left, lift_π]

/-- Every source-action component is the transpose of the literal evaluation after the action. -/
theorem sourceActionMap_π_eq_curry (n a : I) :
    sourceActionMap d S L M N ≫ Pi.π (actionObjects d S L M N) (n, a) =
      MonoidalClosed.curry
        ((ExternalRightModule.sigma d S (diagram d S L M) (action d S L M) n a ▷
            ambientHom d S L M N) ≫
          MonoidalClosed.uncurry (WeightedEndVariance.projection (diagram d S L M) (diagram d S L
            N) (n ⊗ a))) := by
  rw [sourceActionMap_π, MonoidalClosed.enrichedOrdinaryCategorySelf_eHomWhiskerRight]
  simpa only [MonoidalClosed.curry_uncurry] using
    MonoidalClosed.curry_pre_app
      (ExternalRightModule.sigma d S (diagram d S L M) (action d S L M) n a)
      (MonoidalClosed.uncurry (WeightedEndVariance.projection (diagram d S L M) (diagram d S L N)
        (n ⊗ a)))

/-- Every target-action component is the transpose of actual tensor evaluation and the action. -/
theorem targetActionMap_π_eq_curry (n a : I) :
    targetActionMap d S L M N ≫ Pi.π (actionObjects d S L M N) (n, a) =
      MonoidalClosed.curry
        (MonoidalClosed.uncurry
          (WeightedEndVariance.projection (diagram d S L M) (diagram d S L N) n ≫
            (SphereOperator.fixedRightTensor
              (MonoidalClosed.enrichedMonoidalCategoryDataSelf V) (S.obj a)).map
              ((diagram d S L M).toEnrichedFunctor.obj n) ((diagram d S L
                N).toEnrichedFunctor.obj n)) ≫
          ExternalRightModule.sigma d S (diagram d S L N) (action d S L N) n a) := by
  rw [targetActionMap_π, MonoidalClosed.enrichedOrdinaryCategorySelf_eHomWhiskerLeft,
    ← Category.assoc]
  have h := (MonoidalClosed.curry_natural_right
      (A := (diagram d S L M).toEnrichedFunctor.obj n ⊗ S.obj a)
      (MonoidalClosed.uncurry
        (A := (diagram d S L M).toEnrichedFunctor.obj n ⊗ S.obj a)
        (WeightedEndVariance.projection (diagram d S L M) (diagram d S L N) n ≫
          (SphereOperator.fixedRightTensor
            (MonoidalClosed.enrichedMonoidalCategoryDataSelf V) (S.obj a)).map
            ((diagram d S L M).toEnrichedFunctor.obj n) ((diagram d S L N).toEnrichedFunctor.obj
              n)))
      (ExternalRightModule.sigma d S (diagram d S L N) (action d S L N) n a)).symm
  rw [MonoidalClosed.curry_uncurry] at h
  exact h

/-- The two original action/evaluation maps agree as complete morphisms at every index pair. -/
theorem evaluation_action (n a : I) :
    (ExternalRightModule.sigma d S (diagram d S L M) (action d S L M) n a ▷ Hom d S L M N) ≫
        evaluation d S L M N (n ⊗ a) =
      MonoidalClosed.uncurry
        (π d S L M N n ≫
          (SphereOperator.fixedRightTensor
            (MonoidalClosed.enrichedMonoidalCategoryDataSelf V) (S.obj a)).map
            ((diagram d S L M).toEnrichedFunctor.obj n) ((diagram d S L N).toEnrichedFunctor.obj
              n)) ≫
        ExternalRightModule.sigma d S (diagram d S L N) (action d S L N) n a := by
  have h := congrArg MonoidalClosed.uncurry (action_condition d S L M N n a)
  rw [MonoidalClosed.enrichedOrdinaryCategorySelf_eHomWhiskerRight,
    MonoidalClosed.uncurry_pre_app,
    MonoidalClosed.enrichedOrdinaryCategorySelf_eHomWhiskerLeft,
    ← Category.assoc, MonoidalClosed.uncurry_natural_right] at h
  exact h

omit [HasProducts.{uI} V] [HasEqualizers V] in
/-- At the pointed unit the whole action equation is exactly the original stock source square. -/
theorem unit_action_condition_iff (t : (diagram d S L M) ⟶ (diagram d S L N)) :
    (∀ n a,
      t.app (n ⊗ a) ≫
          eHomWhiskerRight V
            (ExternalRightModule.sigma d S (diagram d S L M) (action d S L M) n a)
            ((diagram d S L N).toEnrichedFunctor.obj (n ⊗ a)) =
        t.app n ≫
          (SphereOperator.fixedRightTensor
            (MonoidalClosed.enrichedMonoidalCategoryDataSelf V) (S.obj a)).map
            ((diagram d S L M).toEnrichedFunctor.obj n) ((diagram d S L N).toEnrichedFunctor.obj
              n) ≫
          eHomWhiskerLeft V ((diagram d S L M).toEnrichedFunctor.obj n ⊗ S.obj a)
            (ExternalRightModule.sigma d S (diagram d S L N) (action d S L N) n a)) ↔
      ExternalRightModule.SourceComm d S (diagram d S L M) (diagram d S L N) (action d S L M)
        (action d S L N) t := by
  have hLeft (n a : I) :
      t.app (n ⊗ a) ≫
          eHomWhiskerRight V
            (ExternalRightModule.sigma d S (diagram d S L M) (action d S L M) n a)
            ((diagram d S L N).toEnrichedFunctor.obj (n ⊗ a)) =
        eHomEquiv V
          (ExternalRightModule.sigma d S (diagram d S L M) (action d S L M) n a ≫
            component t (n ⊗ a)) := by
    have hp : eHomEquiv V (component t (n ⊗ a)) = t.app (n ⊗ a) :=
      (eHomEquiv V).apply_symm_apply _
    exact (congrArg (fun p => p ≫ eHomWhiskerRight V
      (ExternalRightModule.sigma d S (diagram d S L M) (action d S L M) n a)
      ((diagram d S L N).toEnrichedFunctor.obj (n ⊗ a))) hp).symm.trans
        (eHomEquiv_comp_eHomWhiskerRight V V
          (ExternalRightModule.sigma d S (diagram d S L M) (action d S L M) n a)
          (component t (n ⊗ a)))
  have hRight (n a : I) :
      t.app n ≫
          (SphereOperator.fixedRightTensor
            (MonoidalClosed.enrichedMonoidalCategoryDataSelf V) (S.obj a)).map
            ((diagram d S L M).toEnrichedFunctor.obj n) ((diagram d S L N).toEnrichedFunctor.obj
              n) ≫
          eHomWhiskerLeft V ((diagram d S L M).toEnrichedFunctor.obj n ⊗ S.obj a)
            (ExternalRightModule.sigma d S (diagram d S L N) (action d S L N) n a) =
        eHomEquiv V
          ((component t n ▷ S.obj a) ≫
            ExternalRightModule.sigma d S (diagram d S L N) (action d S L N) n a) := by
    have ht := SphereOperator.fixedRightTensor_point
      (MonoidalClosed.enrichedMonoidalCategoryDataSelf V) (S.obj a) (component t n)
    have hp : eHomEquiv V (component t n) = t.app n :=
      (eHomEquiv V).apply_symm_apply _
    rw [hp] at ht
    rw [← Category.assoc, ht]
    exact eHomEquiv_comp_eHomWhiskerLeft V V (component t n ▷ S.obj a)
      (ExternalRightModule.sigma d S (diagram d S L N) (action d S L N) n a)
  constructor
  · intro h n a
    apply (eHomEquiv V).injective
    simpa only [tensorHom_id] using (hLeft n a).symm.trans ((h n a).trans (hRight n a))
  · intro h n a
    exact (hLeft n a).trans
      ((congrArg (eHomEquiv V) (by simpa only [tensorHom_id] using h n a)).trans (hRight n a).symm)

/-- A stock module morphism gives its entire genuine enriched compatible unit family. -/
def moduleFamily (f : M ⟶ N) : Family d S L M N (𝟙_ V) where
  transformation := (moduleMap d S L f)
  action_condition := (unit_action_condition_iff d S L M N (moduleMap d S L f)).2
    (ExternalRightModule.stock_source_comm d S L f)

/-- The whole compatible unit family reconstructs the original stock module morphism. -/
def moduleHom (q : Family d S L M N (𝟙_ V)) : M ⟶ N :=
  ExternalRightModule.homOfSourceComm d S L q.transformation
    ((unit_action_condition_iff d S L M N q.transformation).1 q.action_condition)

omit [HasProducts.{uI} V] [HasEqualizers V] in
/-- Reconstruction retains the entire original underlying genuine transformation. -/
theorem moduleHom_hom (q : Family d S L M N (𝟙_ V)) :
    moduleMap d S L (moduleHom d S L M N q) = q.transformation :=
  ExternalRightModule.homOfSourceComm_hom d S L _ _

/-- The complete original stock module Hom is represented by the actual pointed mapping object. -/
def homEquiv : (M ⟶ N) ≃ (𝟙_ V ⟶ Hom d S L M N) where
  toFun f := lift d S L M N (moduleFamily d S L M N f)
  invFun f := moduleHom d S L M N (toFamily d S L M N f)
  left_inv f := by
    apply moduleMap_ext d S L
    rw [moduleHom_hom, toFamily_lift]
    rfl
  right_inv f := by
    apply hom_ext d S L M N
    intro n
    rw [lift_π]
    change (moduleMap d S L (moduleHom d S L M N (toFamily d S L M N f))).app n = _
    rw [moduleHom_hom, toFamily_app]

/-- Every full component of a represented stock module morphism is the original one. -/
@[reassoc]
theorem homEquiv_π (f : M ⟶ N) (n : I) :
    homEquiv d S L M N f ≫ π d S L M N n = (moduleMap d S L f).app n :=
  lift_π d S L M N (moduleFamily d S L M N f) n

/-- Every full component of the reconstructed stock module morphism is the original evaluation. -/
theorem homEquiv_symm_component (f : 𝟙_ V ⟶ Hom d S L M N) (n : I) :
    component (moduleMap d S L ((homEquiv d S L M N).symm f)) n =
      (eHomEquiv V).symm (f ≫ π d S L M N n) := by
  change component (moduleMap d S L (moduleHom d S L M N (toFamily d S L M N f))) n = _
  rw [moduleHom_hom]
  exact congrArg (eHomEquiv V).symm (toFamily_app d S L M N f n)

variable {M N}

/-- Changing the parameter retains the whole enriched family and every original action square. -/
def reparameterize {P Q : V} (h : P ⟶ Q) (q : Family d S L M N Q) : Family d S L M N P where
  transformation := GradedNatTrans.regrade ((Center.ofBraided V).map h) q.transformation
  action_condition n a := by
    simp only [GradedNatTrans.regrade_app]
    change (h ≫ q.transformation.app (n ⊗ a)) ≫ _ =
      (h ≫ q.transformation.app n) ≫ _
    simpa only [Category.assoc] using congrArg (fun r => h ≫ r) (q.action_condition n a)

omit [HasProducts.{uI} V] [HasEqualizers V] in
/-- Every original component changes by the given whole parameter map. -/
theorem reparameterize_app {P Q : V} (h : P ⟶ Q) (q : Family d S L M N Q) (n : I) :
    (reparameterize d S L h q).transformation.app n = h ≫ q.transformation.app n := rfl

/-- The original lift is natural for every actual parameter morphism. -/
@[reassoc]
theorem lift_reparameterize {P Q : V} (h : P ⟶ Q) (q : Family d S L M N Q) :
    lift d S L M N (reparameterize d S L h q) = h ≫ lift d S L M N q := by
  apply hom_ext d S L M N
  intro n
  rw [lift_π, reparameterize_app, Category.assoc, lift_π]

/-- The entire represented family is natural for every original parameter map. -/
theorem toFamily_precomp {P Q : V} (h : P ⟶ Q) (f : Q ⟶ Hom d S L M N) :
    toFamily d S L M N (h ≫ f) = reparameterize d S L h (toFamily d S L M N f) := by
  apply Family.ext
  apply GradedNatTrans.ext
  funext n
  rw [toFamily_app, reparameterize_app, toFamily_app, Category.assoc]

variable {K : Module d S L}

/-- Compose complete compatible families in the actual source-first tensor grade. -/
def composeFamily {P Q : V} (q : Family d S L M N P) (r : Family d S L N K Q) :
    Family d S L M K (P ⊗ Q) where
  transformation := GradedNatTrans.regrade (Functor.OplaxMonoidal.δ (Center.ofBraided V) P Q)
    (GradedNatTrans.tensorComp q.transformation r.transformation)
  action_condition n a := by
    simp only [GradedNatTrans.regrade_app, Center.ofBraided_δ_f, Category.id_comp,
      GradedNatTrans.tensorComp_app]
    simpa only [Category.assoc] using
      MappingCompositionAlgebra.compose_right_action
        ((diagram d S L M).toEnrichedFunctor.obj n) ((diagram d S L M).toEnrichedFunctor.obj (n ⊗
          a))
        ((diagram d S L N).toEnrichedFunctor.obj n) ((diagram d S L N).toEnrichedFunctor.obj (n ⊗
          a))
        ((diagram d S L K).toEnrichedFunctor.obj n) ((diagram d S L K).toEnrichedFunctor.obj (n ⊗
          a)) (S.obj a)
        (ExternalRightModule.sigma d S (diagram d S L M) (action d S L M) n a)
        (ExternalRightModule.sigma d S (diagram d S L N) (action d S L N) n a)
        (ExternalRightModule.sigma d S (diagram d S L K) (action d S L K) n a)
        (q.transformation.app n) (q.transformation.app (n ⊗ a))
        (r.transformation.app n) (r.transformation.app (n ⊗ a))
        (q.action_condition n a) (r.action_condition n a)

omit [HasProducts.{uI} V] [HasEqualizers V] in
/-- Both complete parameter factors are retained by composition at every index object. -/
theorem composeFamily_app {P Q : V} (q : Family d S L M N P) (r : Family d S L N K Q) (n : I) :
    (composeFamily d S L q r).transformation.app n =
      (q.transformation.app n ⊗ₘ r.transformation.app n) ≫
        eComp V ((diagram d S L M).toEnrichedFunctor.obj n) ((diagram d S L
          N).toEnrichedFunctor.obj n)
          ((diagram d S L K).toEnrichedFunctor.obj n) := by
  simp only [composeFamily, GradedNatTrans.regrade_app, Center.ofBraided_δ_f,
    Category.id_comp, GradedNatTrans.tensorComp_app]

/-- The actual enriched identity is the whole original stock module identity. -/
def identity (M : Module d S L) : 𝟙_ V ⟶ Hom d S L M M := homEquiv d S L M M (𝟙 M)

/-- Every entire identity component is the original internal-Hom identity. -/
@[reassoc]
theorem identity_π (M : Module d S L) (n : I) :
    identity d S L M ≫ π d S L M M n = eId V ((diagram d S L M).toEnrichedFunctor.obj n) := by
  rw [identity, homEquiv_π]
  exact GradedNatTrans.unitId_app (diagram d S L M).toEnrichedFunctor n

/-- Source-first enriched composition descends both complete mapping objects through the
  equalizer. -/
def composition (M N K : Module d S L) :
    Hom d S L M N ⊗ Hom d S L N K ⟶ Hom d S L M K :=
  lift d S L M K
    (composeFamily d S L (toFamily d S L M N (𝟙 (Hom d S L M N)))
      (toFamily d S L N K (𝟙 (Hom d S L N K))))

/-- Every complete composition component is the tensor of the two original Hom components. -/
@[reassoc]
theorem composition_π (M N K : Module d S L) (n : I) :
    composition d S L M N K ≫ π d S L M K n =
      (π d S L M N n ⊗ₘ π d S L N K n) ≫
        eComp V ((diagram d S L M).toEnrichedFunctor.obj n) ((diagram d S L
          N).toEnrichedFunctor.obj n)
          ((diagram d S L K).toEnrichedFunctor.obj n) := by
  rw [composition, lift_π, composeFamily_app, toFamily_app, toFamily_app,
    Category.id_comp, Category.id_comp]

/-- Actual enriched composition is left unital on the entire original mapping object. -/
theorem identity_composition (M N : Module d S L) :
    (λ_ (Hom d S L M N)).inv ≫ identity d S L M ▷ Hom d S L M N ≫
      composition d S L M M N = 𝟙 (Hom d S L M N) := by
  apply hom_ext d S L M N
  intro n
  rw [Category.assoc, Category.assoc, composition_π, Category.id_comp,
    tensorHom_def, Category.assoc, ← comp_whiskerRight_assoc, identity_π,
    ← whisker_exchange_assoc, id_whiskerLeft, Category.assoc, Category.assoc,
    Iso.inv_hom_id_assoc]
  exact (congrArg (fun f => π d S L M N n ≫ f)
    (e_id_comp V ((diagram d S L M).toEnrichedFunctor.obj n) ((diagram d S L
      N).toEnrichedFunctor.obj n))).trans
      (Category.comp_id _)

/-- Actual enriched composition is right unital on the entire original mapping object. -/
theorem composition_identity (M N : Module d S L) :
    (ρ_ (Hom d S L M N)).inv ≫ Hom d S L M N ◁ identity d S L N ≫
      composition d S L M N N = 𝟙 (Hom d S L M N) := by
  apply hom_ext d S L M N
  intro n
  rw [Category.assoc, Category.assoc, composition_π, Category.id_comp,
    tensorHom_def', Category.assoc, ← whiskerLeft_comp_assoc, identity_π,
    whisker_exchange_assoc, whiskerRight_id, Category.assoc, Category.assoc,
    Iso.inv_hom_id_assoc]
  exact (congrArg (fun f => π d S L M N n ≫ f)
    (e_comp_id V ((diagram d S L M).toEnrichedFunctor.obj n) ((diagram d S L
      N).toEnrichedFunctor.obj n))).trans
      (Category.comp_id _)

/-- Source-first composition is associative on the entire three-factor mapping object. -/
theorem composition_associativity (J M N K : Module d S L) :
    (α_ (Hom d S L J M) (Hom d S L M N) (Hom d S L N K)).inv ≫
        composition d S L J M N ▷ Hom d S L N K ≫ composition d S L J N K =
      Hom d S L J M ◁ composition d S L M N K ≫ composition d S L J M K := by
  apply hom_ext d S L J K
  intro n
  conv_lhs =>
    rw [Category.assoc, Category.assoc, composition_π,
      tensorHom_def_assoc, ← comp_whiskerRight_assoc, composition_π,
      comp_whiskerRight_assoc, ← whisker_exchange_assoc,
      ← whisker_exchange_assoc, ← tensorHom_def'_assoc, ← associator_inv_naturality_assoc]
  conv_rhs =>
    rw [Category.assoc, composition_π, tensorHom_def'_assoc,
      ← whiskerLeft_comp_assoc, composition_π,
      whiskerLeft_comp_assoc, whisker_exchange_assoc,
      whisker_exchange_assoc, ← tensorHom_def_assoc]
  exact congrArg (fun f => (π d S L J M n ⊗ₘ (π d S L M N n ⊗ₘ π d S L N K n)) ≫ f)
    (e_assoc V ((diagram d S L J).toEnrichedFunctor.obj n) ((diagram d S L
      M).toEnrichedFunctor.obj n)
      ((diagram d S L N).toEnrichedFunctor.obj n) ((diagram d S L K).toEnrichedFunctor.obj n))

/-- The complete stock module Hom correspondence preserves the original identity. -/
theorem homEquiv_id (M : Module d S L) : homEquiv d S L M M (𝟙 M) = identity d S L M := rfl

/-- The complete stock module Hom correspondence preserves actual source-first composition. -/
theorem homEquiv_comp {M N K : Module d S L} (f : M ⟶ N) (g : N ⟶ K) :
    homEquiv d S L M K (f ≫ g) = (λ_ (𝟙_ V)).inv ≫
      (homEquiv d S L M N f ⊗ₘ homEquiv d S L N K g) ≫ composition d S L M N K := by
  apply hom_ext d S L M K
  intro n
  simp only [Category.assoc, composition_π, tensorHom_comp_tensorHom_assoc, homEquiv_π]
  exact GradedNatTrans.unitComp_app (moduleMap d S L f) (moduleMap d S L g) n

/-- Actual source variance composes with the entire represented stock module map. -/
def pre {M' M : Module d S L} (f : M' ⟶ M) (N : Module d S L) :
    Hom d S L M N ⟶ Hom d S L M' N :=
  (λ_ (Hom d S L M N)).inv ≫
    (homEquiv d S L M' M f ⊗ₘ 𝟙 (Hom d S L M N)) ≫ composition d S L M' M N

/-- Actual target variance composes with the entire represented stock module map. -/
def post (M : Module d S L) {N N' : Module d S L} (g : N ⟶ N') :
    Hom d S L M N ⟶ Hom d S L M N' :=
  (ρ_ (Hom d S L M N)).inv ≫
    (𝟙 (Hom d S L M N) ⊗ₘ homEquiv d S L N N' g) ≫ composition d S L M N N'

/-- Source variance is literal internal-Hom precomposition on every entire component. -/
@[reassoc]
theorem pre_π {M' M : Module d S L} (f : M' ⟶ M) (N : Module d S L) (n : I) :
    pre d S L f N ≫ π d S L M' N n =
      π d S L M N n ≫ eHomWhiskerRight V (component (moduleMap d S L f) n) ((diagram d S L
        N).toEnrichedFunctor.obj n) := by
  rw [pre, Category.assoc, Category.assoc, composition_π,
    tensorHom_comp_tensorHom_assoc, homEquiv_π, Category.id_comp]
  have hp : (moduleMap d S L f).app n = eHomEquiv V (component (moduleMap d S L f) n) :=
    ((eHomEquiv V).apply_symm_apply ((moduleMap d S L f).app n)).symm
  rw [hp]
  simp only [eHomWhiskerRight, tensorHom_def', Category.assoc]
  rw [← leftUnitor_inv_naturality_assoc]
  rfl

/-- Target variance is literal internal-Hom postcomposition on every entire component. -/
@[reassoc]
theorem post_π (M : Module d S L) {N N' : Module d S L} (g : N ⟶ N') (n : I) :
    post d S L M g ≫ π d S L M N' n =
      π d S L M N n ≫ eHomWhiskerLeft V ((diagram d S L M).toEnrichedFunctor.obj n) (component
        (moduleMap d S L g) n) := by
  rw [post, Category.assoc, Category.assoc, composition_π,
    tensorHom_comp_tensorHom_assoc, homEquiv_π, Category.id_comp]
  have hp : (moduleMap d S L g).app n = eHomEquiv V (component (moduleMap d S L g) n) :=
    ((eHomEquiv V).apply_symm_apply ((moduleMap d S L g).app n)).symm
  rw [hp]
  simp only [eHomWhiskerLeft, tensorHom_def, Category.assoc]
  rw [← rightUnitor_inv_naturality_assoc]
  rfl

/-- Source variance retains the whole original ambient weighted-end source map. -/
@[reassoc]
theorem pre_ι {M' M : Module d S L} (f : M' ⟶ M) (N : Module d S L) :
    pre d S L f N ≫ ι d S L M' N =
      ι d S L M N ≫ WeightedEndVariance.pre (moduleMap d S L f) (diagram d S L N) := by
  apply weightedEnd.hom_ext (diagram d S L M').toEnrichedFunctor (diagram d S L N).toEnrichedFunctor
  intro n
  simp only [Category.assoc]
  change pre d S L f N ≫ π d S L M' N n =
    ι d S L M N ≫ (WeightedEndVariance.pre (moduleMap d S L f) (diagram d S L N) ≫
      WeightedEndVariance.projection (diagram d S L M') (diagram d S L N) n)
  rw [pre_π, WeightedEndVariance.pre_projection,
    MonoidalClosed.enrichedOrdinaryCategorySelf_eHomWhiskerRight]
  exact Category.assoc _ _ _

/-- Target variance retains the whole original ambient weighted-end target map. -/
@[reassoc]
theorem post_ι (M : Module d S L) {N N' : Module d S L} (g : N ⟶ N') :
    post d S L M g ≫ ι d S L M N' =
      ι d S L M N ≫ WeightedEndVariance.post (diagram d S L M) (moduleMap d S L g) := by
  apply weightedEnd.hom_ext (diagram d S L M).toEnrichedFunctor (diagram d S L N').toEnrichedFunctor
  intro n
  simp only [Category.assoc]
  change post d S L M g ≫ π d S L M N' n =
    ι d S L M N ≫ (WeightedEndVariance.post (diagram d S L M) (moduleMap d S L g) ≫
      WeightedEndVariance.projection (diagram d S L M) (diagram d S L N') n)
  rw [post_π, WeightedEndVariance.post_projection,
    MonoidalClosed.enrichedOrdinaryCategorySelf_eHomWhiskerLeft]
  exact Category.assoc _ _ _

/-- Actual source variance preserves the entire stock identity map. -/
theorem pre_id (M N : Module d S L) : pre d S L (𝟙 M) N = 𝟙 (Hom d S L M N) := by
  simpa only [pre, homEquiv_id, tensorHom_id] using identity_composition d S L M N

/-- Actual target variance preserves the entire stock identity map. -/
theorem post_id (M N : Module d S L) : post d S L M (𝟙 N) = 𝟙 (Hom d S L M N) := by
  simpa only [post, homEquiv_id, id_tensorHom] using composition_identity d S L M N

/-- Source variance preserves the complete original contravariant order of composition. -/
theorem pre_comp {J M N : Module d S L} (f : J ⟶ M) (g : M ⟶ N) (K : Module d S L) :
    pre d S L (f ≫ g) K = pre d S L g K ≫ pre d S L f K := by
  apply equalizer.hom_ext
  change pre d S L (f ≫ g) K ≫ ι d S L J K =
    (pre d S L g K ≫ pre d S L f K) ≫ ι d S L J K
  rw [pre_ι, Category.assoc, pre_ι, ← Category.assoc, pre_ι, Category.assoc]
  change ι d S L N K ≫ WeightedEndVariance.pre ((moduleMap d S L f) ≫ (moduleMap d S L g))
    (diagram d S L K) = _
  rw [WeightedEndVariance.pre_comp]

/-- Target variance preserves both complete original stock module maps. -/
theorem post_comp (J : Module d S L) {M N K : Module d S L} (f : M ⟶ N) (g : N ⟶ K) :
    post d S L J (f ≫ g) = post d S L J f ≫ post d S L J g := by
  apply equalizer.hom_ext
  change post d S L J (f ≫ g) ≫ ι d S L J K =
    (post d S L J f ≫ post d S L J g) ≫ ι d S L J K
  rw [post_ι, Category.assoc, post_ι, ← Category.assoc, post_ι, Category.assoc]
  change ι d S L J M ≫ WeightedEndVariance.post (diagram d S L J) ((moduleMap d S L f) ≫
    (moduleMap d S L g)) = _
  rw [WeightedEndVariance.post_comp]

/-- Complete source and target variance commute on the actual module mapping end. -/
theorem pre_post {M' M N N' : Module d S L} (f : M' ⟶ M) (g : N ⟶ N') :
    post d S L M g ≫ pre d S L f N' = pre d S L f N ≫ post d S L M' g := by
  apply equalizer.hom_ext
  change (post d S L M g ≫ pre d S L f N') ≫ ι d S L M' N' =
    (pre d S L f N ≫ post d S L M' g) ≫ ι d S L M' N'
  conv_lhs => rw [Category.assoc, pre_ι, ← Category.assoc, post_ι, Category.assoc]
  conv_rhs => rw [Category.assoc, post_ι, ← Category.assoc, pre_ι, Category.assoc]
  exact congrArg (fun h => ι d S L M N ≫ h) (WeightedEndVariance.pre_post (moduleMap d S L f)
    (moduleMap d S L g))

/-- Both original module maps give the full mapping-object bifunctor. -/
def rightFunctor (M : Module d S L) : Module d S L ⥤ V where
  obj N := Hom d S L M N
  map f := post d S L M f
  map_id N := post_id d S L M N
  map_comp f g := post_comp d S L M f g

/-- The actual enriched module mapping end is contravariant and covariant on whole stock modules. -/
def bifunctor : (Module d S L)ᵒᵖ ⥤ Module d S L ⥤ V where
  obj M := rightFunctor d S L M.unop
  map f :=
    { app N := pre d S L f.unop N
      naturality _ _ g := pre_post d S L f.unop g }
  map_id M := by
    apply NatTrans.ext
    funext N
    exact pre_id d S L M.unop N
  map_comp f g := by
    apply NatTrans.ext
    funext N
    exact pre_comp d S L g.unop f.unop N

/-- The constructed equalizers genuinely enrich the original stock module objects. -/
@[instance_reducible]
def enrichedCategory : EnrichedCategory V (Module d S L) where
  Hom := Hom d S L
  id := identity d S L
  comp := composition d S L
  id_comp := identity_composition d S L
  comp_id := composition_identity d S L
  assoc := composition_associativity d S L

/-- The full original stock category has the constructed enriched Hom, identity and composition. -/
@[instance_reducible]
def enrichedOrdinaryCategory : EnrichedOrdinaryCategory V (Module d S L) where
  toEnrichedCategory := enrichedCategory d S L
  homEquiv := homEquiv d S L _ _
  homEquiv_id := homEquiv_id d S L
  homEquiv_comp := homEquiv_comp d S L

end CategoryTheory.Enriched.SphereModuleMappingEnd
