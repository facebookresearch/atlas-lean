/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

import MathlibExt.CategoryTheory.Enriched.SphereModuleMappingEnd
import Lean.Util.CollectAxioms

/-!
# Clients of the full stock module mapping end

These clients spell the original stock fields, both complete action arrows,
the universal property at arbitrary parameters, and the evaluation formulas
for variance and source-first composition. No native Day closed structure or
module mapping-object witness is an input.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

universe uV vV uI vI

open CategoryTheory CategoryTheory.Limits MonoidalCategory BraidedCategory
open scoped MonoidalClosed CategoryTheory.MonObj

namespace CategoryTheory.Enriched.SphereModuleMappingEndTests

open EnrichedFunctorCat EnrichedDayKernel SphereModuleMappingEnd
attribute [local instance] SphereModuleMappingEnd.moduleCategory
attribute [local instance] ColimitMonoidal.smallestColimits
attribute [local instance] MonoidalLeftAction.monoidalOppositeLeftAction

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [SymmetricCategory V] [MonoidalClosed V]
  {I : Type uI} [Category.{vI} I] [MonoidalCategory I]
  [EnrichedOrdinaryCategory V I] [HasColimitsOfSize.{uI, uI} V]
  [HasProducts.{uI} V] [HasEqualizers V]
  (d : EnrichedMonoidalCategoryData V I) (S : EnrichedFunctor V I V)
  (L : EnrichedFunctor.LaxMonoidalData d
    (MonoidalClosed.enrichedMonoidalCategoryDataSelf V) S)

omit [HasProducts.{uI} V] [HasEqualizers V] in
/-- The producer retains the literal stock carrier, diagram and action. -/
theorem original_stock_fields (M : Module d S L) :
    letI := ColimitMonoidal.monoidalCategory d
    letI := LaxMonoid.monObj d S L
    diagram d S L M = M.X ∧ action d S L M = M.action := by
  let : MonoidalCategory (EnrichedFunctorCat V I) := ColimitMonoidal.monoidalCategory d
  let : MonObj (⟨S⟩ : EnrichedFunctorCat V I) := LaxMonoid.monObj d S L
  exact ⟨rfl, rfl⟩

omit [HasProducts.{uI} V] [HasEqualizers V] in
/-- All full output-Hom labels retain the original Day-action generator. -/
theorem every_action_label (M : Module d S L) (k n a : I) :
    gen d.tensorEnrichedFunctor (diagram d S L M).toEnrichedFunctor S k (n, a) ≫
        component (action d S L M) k =
      (𝟙 ((n ⊗ a) ⟶[V] k) ⊗ₘ
        ExternalRightModule.sigma d S (diagram d S L M) (action d S L M) n a) ≫
        ActionFromTransformation.targetAction (diagram d S L M).toEnrichedFunctor (n ⊗ a) k :=
  ExternalRightModule.gen_action d S (diagram d S L M) (action d S L M) k n a

/-- The entire source arrow is the original closed precomposition map at every pair. -/
theorem source_arrow (M N : Module d S L) (n a : I) :
    sourceActionMap d S L M N ≫ Pi.π (actionObjects d S L M N) (n, a) =
      weightedEnd.π (diagram d S L M).toEnrichedFunctor
        (diagram d S L N).toEnrichedFunctor (n ⊗ a) ≫
        (MonoidalClosed.pre
          (ExternalRightModule.sigma d S (diagram d S L M) (action d S L M) n a)).app
          ((diagram d S L N).toEnrichedFunctor.obj (n ⊗ a)) := by
  rw [sourceActionMap_π, MonoidalClosed.enrichedOrdinaryCategorySelf_eHomWhiskerRight]

/-- The entire target arrow uses the original enriched tensor and closed postcomposition. -/
theorem target_arrow (M N : Module d S L) (n a : I) :
    targetActionMap d S L M N ≫ Pi.π (actionObjects d S L M N) (n, a) =
      weightedEnd.π (diagram d S L M).toEnrichedFunctor
        (diagram d S L N).toEnrichedFunctor n ≫
        (SphereOperator.fixedRightTensor
          (MonoidalClosed.enrichedMonoidalCategoryDataSelf V) (S.obj a)).map
          ((diagram d S L M).toEnrichedFunctor.obj n)
          ((diagram d S L N).toEnrichedFunctor.obj n) ≫
        (ihom ((diagram d S L M).toEnrichedFunctor.obj n ⊗ S.obj a)).map
          (ExternalRightModule.sigma d S (diagram d S L N) (action d S L N) n a) := by
  rw [targetActionMap_π, MonoidalClosed.enrichedOrdinaryCategorySelf_eHomWhiskerLeft]

/-- The mapping object is the actual full ambient-end action equalizer. -/
theorem actual_equalizer (M N : Module d S L) :
    Hom d S L M N = equalizer
      (Pi.lift fun p : I × I =>
        weightedEnd.π (diagram d S L M).toEnrichedFunctor
          (diagram d S L N).toEnrichedFunctor (p.1 ⊗ p.2) ≫
          eHomWhiskerRight V
            (ExternalRightModule.sigma d S (diagram d S L M) (action d S L M) p.1 p.2)
            ((diagram d S L N).toEnrichedFunctor.obj (p.1 ⊗ p.2)))
      (Pi.lift fun p : I × I =>
        weightedEnd.π (diagram d S L M).toEnrichedFunctor
          (diagram d S L N).toEnrichedFunctor p.1 ≫
          (SphereOperator.fixedRightTensor
            (MonoidalClosed.enrichedMonoidalCategoryDataSelf V) (S.obj p.2)).map
            ((diagram d S L M).toEnrichedFunctor.obj p.1)
            ((diagram d S L N).toEnrichedFunctor.obj p.1) ≫
          eHomWhiskerLeft V ((diagram d S L M).toEnrichedFunctor.obj p.1 ⊗ S.obj p.2)
            (ExternalRightModule.sigma d S (diagram d S L N) (action d S L N) p.1 p.2)) := rfl

/-- The constructed mapping object is the limit of the two original full action arrows. -/
def original_equalizer_limit (M N : Module d S L) :
    IsLimit (Fork.ofι (ι d S L M N) (condition d S L M N)) := forkIsLimit d S L M N

/-- Every compatible genuine enriched transformation at any parameter has a unique full lift. -/
theorem universal_property (M N : Module d S L) (P : V)
    (t : GradedNatTrans ((Center.ofBraided V).obj P)
      (diagram d S L M).toEnrichedFunctor (diagram d S L N).toEnrichedFunctor)
    (h : ∀ n a,
      t.app (n ⊗ a) ≫
          (MonoidalClosed.pre
            (ExternalRightModule.sigma d S (diagram d S L M) (action d S L M) n a)).app
            ((diagram d S L N).toEnrichedFunctor.obj (n ⊗ a)) =
        t.app n ≫
          (SphereOperator.fixedRightTensor
            (MonoidalClosed.enrichedMonoidalCategoryDataSelf V) (S.obj a)).map
            ((diagram d S L M).toEnrichedFunctor.obj n)
            ((diagram d S L N).toEnrichedFunctor.obj n) ≫
          (ihom ((diagram d S L M).toEnrichedFunctor.obj n ⊗ S.obj a)).map
            (ExternalRightModule.sigma d S (diagram d S L N) (action d S L N) n a)) :
    ∃! f : P ⟶ Hom d S L M N, ∀ n, f ≫ π d S L M N n = t.app n := by
  let q : Family d S L M N P := {
    transformation := t
    action_condition := fun n a => by
      rw [MonoidalClosed.enrichedOrdinaryCategorySelf_eHomWhiskerRight,
        MonoidalClosed.enrichedOrdinaryCategorySelf_eHomWhiskerLeft]
      exact h n a }
  refine ⟨lift d S L M N q, ?_, ?_⟩
  · intro n
    exact lift_π d S L M N q n
  · intro f hf
    exact lift_unique d S L M N q f hf

/-- The complete evaluation characteristic determines the unique lift at arbitrary parameters. -/
theorem evaluation_universal_property (M N : Module d S L) (P : V)
    (q : Family d S L M N P) (f : P ⟶ Hom d S L M N)
    (h : ∀ n, ((diagram d S L M).toEnrichedFunctor.obj n ◁ f) ≫
      SphereModuleMappingEnd.evaluation d S L M N n = MonoidalClosed.uncurry
        (q.transformation.app n)) :
    f = lift d S L M N q := by
  apply lift_unique d S L M N q f
  intro n
  apply MonoidalClosed.uncurry_injective
  rw [MonoidalClosed.uncurry_natural_left]
  exact h n

/-- Source variance commutes with every entire original evaluation map. -/
theorem source_evaluation {M' M : Module d S L} (f : M' ⟶ M) (N : Module d S L) (n : I) :
    ((diagram d S L M').toEnrichedFunctor.obj n ◁ pre d S L f N) ≫
        SphereModuleMappingEnd.evaluation d S L M' N n =
      (component (moduleMap d S L f) n ▷ Hom d S L M N) ≫ SphereModuleMappingEnd.evaluation d S L
        M N n := by
  have h := congrArg MonoidalClosed.uncurry (pre_π d S L f N n)
  rw [MonoidalClosed.uncurry_natural_left,
    MonoidalClosed.enrichedOrdinaryCategorySelf_eHomWhiskerRight,
    MonoidalClosed.uncurry_pre_app] at h
  exact h

/-- Target variance commutes with every entire original evaluation map. -/
theorem target_evaluation (M : Module d S L) {N N' : Module d S L} (g : N ⟶ N') (n : I) :
    ((diagram d S L M).toEnrichedFunctor.obj n ◁ post d S L M g) ≫
        SphereModuleMappingEnd.evaluation d S L M N' n =
      SphereModuleMappingEnd.evaluation d S L M N n ≫ component (moduleMap d S L g) n := by
  have h := congrArg MonoidalClosed.uncurry (post_π d S L M g n)
  rw [MonoidalClosed.uncurry_natural_left,
    MonoidalClosed.enrichedOrdinaryCategorySelf_eHomWhiskerLeft,
    MonoidalClosed.uncurry_natural_right] at h
  exact h

/-- Composition evaluates the two complete original mapping objects in source-first order. -/
theorem composition_evaluation (M N K : Module d S L) (n : I) :
    ((diagram d S L M).toEnrichedFunctor.obj n ◁ composition d S L M N K) ≫
        SphereModuleMappingEnd.evaluation d S L M K n =
      (α_ ((diagram d S L M).toEnrichedFunctor.obj n)
        (Hom d S L M N) (Hom d S L N K)).inv ≫
        (SphereModuleMappingEnd.evaluation d S L M N n ▷ Hom d S L N K) ≫
          SphereModuleMappingEnd.evaluation d S L N K n := by
  rw [SphereModuleMappingEnd.evaluation, ← MonoidalClosed.uncurry_natural_left, composition_π]
  exact MonoidalClosed.uncurry_eComp (π d S L M N n) (π d S L N K n)

/-- The constructed stock enrichment uses the complete original module Hom correspondence. -/
theorem enriched_stock_component (M N : Module d S L) (f : M ⟶ N) (n : I) :
    letI := enrichedOrdinaryCategory d S L
    eHomEquiv V f ≫ π d S L M N n = (moduleMap d S L f).app n :=
  homEquiv_π d S L M N f n

/-- The inverse stock Hom correspondence recovers every entire original component. -/
theorem original_module_inverse (M N : Module d S L) (f : M ⟶ N) :
    (homEquiv d S L M N).symm (homEquiv d S L M N f) = f :=
  (homEquiv d S L M N).symm_apply_apply f

end CategoryTheory.Enriched.SphereModuleMappingEndTests

open Lean in
#eval show MetaM Unit from do
  let env := (← getEnv).setExporting false
  let mod := `MathlibExt.CategoryTheory.Enriched.SphereModuleMappingEnd
  let some idx := env.getModuleIdx? mod | throwError "Missing module mapping-end producer"
  let names := env.constants.fold (init := #[]) fun ns n ci =>
    if env.getModuleIdxFor? n == some idx then ns.push (n, ci) else ns
  unless !names.isEmpty do throwError "Empty module mapping-end producer"
  for (n, ci) in names do
    if ci.isUnsafe then throwError "Unsafe module mapping-end declaration {n}"
    let axs ← Lean.collectAxioms n
    let bad := axs.filter fun a => a != ``propext && a != ``Classical.choice && a != ``Quot.sound
    unless bad.isEmpty do throwError "Forbidden module mapping-end axioms {n}: {bad}"
  IO.println s!"Module mapping end: {names.size} safe declarations, standard logical axioms only."
