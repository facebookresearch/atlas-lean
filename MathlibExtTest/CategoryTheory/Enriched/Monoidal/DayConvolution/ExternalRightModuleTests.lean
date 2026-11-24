/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

import MathlibExt.CategoryTheory.Enriched.Monoidal.DayConvolution.ExternalRightModuleCorrespondence
import Batteries.Tactic.Lint
import Lean

set_option autoImplicit false
set_option maxRecDepth 512

noncomputable section
universe uV vV uI vI

open CategoryTheory Limits MonoidalCategory BraidedCategory
open scoped MonoidalClosed

namespace MathlibExtTest.ExternalRightModule

open EnrichedFunctorCat EnrichedDayKernel EnrichedDayKernel.ExternalRightModule
attribute [local instance] Enriched.prodCategory ColimitMonoidal.smallestColimits
attribute [local instance] MonoidalLeftAction.monoidalOppositeLeftAction

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [SymmetricCategory V] [MonoidalClosed V]
  {I : Type uI} [Category.{vI} I] [MonoidalCategory I]
  [EnrichedOrdinaryCategory V I] [HasColimitsOfSize.{uI, uI} V]
  (d : EnrichedMonoidalCategoryData V I) (S : EnrichedFunctor V I V)
  (L : EnrichedFunctor.LaxMonoidalData d (MonoidalClosed.enrichedMonoidalCategoryDataSelf V) S)

section Actions

variable (R R' : EnrichedFunctorCat V I) (a : Action d S R) (b : Action d S R')
  (f : R ⟶ R')

example : descend d S R (external d S R a) = a := descend_external d S R a

example (t : Transformation d S R) : external d S R (descend d S R t) = t := external_descend d S R t

/-- The entire Day generator family retains its full output-Hom coefficient object. -/
theorem whole_action :
    (fun (k : I) (x : I × I) => gen d.tensorEnrichedFunctor R.toEnrichedFunctor S k x ≫ component a k) =
    (fun (k : I) (x : I × I) =>
      (𝟙 ((x.1 ⊗ x.2) ⟶[V] k) ⊗ₘ sigma d S R a x.1 x.2) ≫
        ActionFromTransformation.targetAction R.toEnrichedFunctor (x.1 ⊗ x.2) k) := by
  funext k x
  exact gen_action d S R a k x.1 x.2

/-- All left triple coend generators retain two actual external actions. -/
theorem whole_left :
    (fun (k : I) (x : (I × I) × I) =>
      AssociatorFlat.leftGenerator d R.toEnrichedFunctor S S k x ≫
        AssociatorFlattening.flatToNested d R.toEnrichedFunctor S S k ≫
        Input.mapAt d.tensorEnrichedFunctor a (GradedNatTrans.unitId S) k ≫ component a k) =
    (fun (k : I) (x : (I × I) × I) =>
      (𝟙 (((x.1.1 ⊗ x.1.2) ⊗ x.2) ⟶[V] k) ⊗ₘ
        ((sigma d S R a x.1.1 x.1.2 ▷ S.obj x.2) ≫ sigma d S R a (x.1.1 ⊗ x.1.2) x.2)) ≫
          ActionFromTransformation.targetAction R.toEnrichedFunctor ((x.1.1 ⊗ x.1.2) ⊗ x.2) k) := by
  funext k x
  exact leftFlat_action d S R a k x

/-- All right triple coend generators retain the actual lax tensorator. -/
theorem whole_right :
    (fun (k : I) (x : (I × I) × I) =>
      AssociatorFlat.rightGenerator d R.toEnrichedFunctor S S k x ≫
        AssociatorRightFlattening.flatToNested d R.toEnrichedFunctor S S k ≫
        Input.mapAt d.tensorEnrichedFunctor (GradedNatTrans.unitId R.toEnrichedFunctor) (LaxMonoid.multiply d S L) k ≫
        component a k) =
    (fun (k : I) (x : (I × I) × I) =>
      (𝟙 ((x.1.1 ⊗ (x.1.2 ⊗ x.2)) ⟶[V] k) ⊗ₘ
        ((R.toEnrichedFunctor.obj x.1.1 ◁ L.mu x.1.2 x.2) ≫ sigma d S R a x.1.1 (x.1.2 ⊗ x.2))) ≫
          ActionFromTransformation.targetAction R.toEnrichedFunctor (x.1.1 ⊗ (x.1.2 ⊗ x.2)) k) := by
  funext k x
  exact rightFlat_action d S L R a k x

/-- Postcomposition retains the full output-Hom action, on all inputs and all outputs. -/
theorem whole_action_comp :
    (fun (k : I) (x : I × I) =>
      gen d.tensorEnrichedFunctor R.toEnrichedFunctor S k x ≫ component (a ≫ f) k) =
    (fun (k : I) (x : I × I) =>
      (𝟙 ((x.1 ⊗ x.2) ⟶[V] k) ⊗ₘ (sigma d S R a x.1 x.2 ≫ component f (x.1 ⊗ x.2))) ≫
        ActionFromTransformation.targetAction R'.toEnrichedFunctor (x.1 ⊗ x.2) k) := by
  funext k x
  exact gen_action_comp d S R R' a f k x.1 x.2

/-- Input naturality retains that same full output-Hom action on every coefficient object. -/
theorem whole_input_action :
    (fun (k : I) (x : I × I) =>
      gen d.tensorEnrichedFunctor R.toEnrichedFunctor S k x ≫
        component (Input.natTrans d.tensorEnrichedFunctor f (GradedNatTrans.unitId S) ≫ b) k) =
    (fun (k : I) (x : I × I) =>
      (𝟙 ((x.1 ⊗ x.2) ⟶[V] k) ⊗ₘ ((component f x.1 ⊗ₘ 𝟙 (S.obj x.2)) ≫ sigma d S R' b x.1 x.2)) ≫
        ActionFromTransformation.targetAction R'.toEnrichedFunctor (x.1 ⊗ x.2) k) := by
  funext k x
  exact gen_input_action d S R R' f b k x.1 x.2

example : (∀ n j : I, sigma d S R a n j ≫ component f (n ⊗ j) =
    (component f n ⊗ₘ 𝟙 (S.obj j)) ≫ sigma d S R' b n j) ↔
    a ≫ f = Input.natTrans d.tensorEnrichedFunctor f (GradedNatTrans.unitId S) ≫ b :=
  comm_iff d S R R' a b f

end Actions

section Converse

variable (R : EnrichedFunctorCat V I) (t : Transformation d S R)
  (hu : ∀ n : I, (R.toEnrichedFunctor.obj n ◁ L.epsilon) ≫ (eHomEquiv V).symm (t.app (n, 𝟙_ I)) ≫
    R.toEnrichedFunctor.toOrdinaryFunctor.map (ρ_ n).hom = (ρ_ (R.toEnrichedFunctor.obj n)).hom)
  (ha : ∀ n j b : I, (α_ (R.toEnrichedFunctor.obj n) (S.obj j) (S.obj b)).inv ≫
    ((eHomEquiv V).symm (t.app (n, j)) ▷ S.obj b) ≫ (eHomEquiv V).symm (t.app (n ⊗ j, b)) =
    (R.toEnrichedFunctor.obj n ◁ L.mu j b) ≫ (eHomEquiv V).symm (t.app (n, j ⊗ b)) ≫
      R.toEnrichedFunctor.toOrdinaryFunctor.map (α_ n j b).inv)

/-- The lawful action is chosen by passing the genuine transformation explicitly. -/
example : letI := ColimitMonoidal.monoidalCategory d
    letI := LaxMonoid.monObj d S L
    ModObj (MonoidalOpposite.mop (⟨S⟩ : EnrichedFunctorCat V I)) R := by
  let : MonoidalCategory (EnrichedFunctorCat V I) := ColimitMonoidal.monoidalCategory d
  let : MonObj (⟨S⟩ : EnrichedFunctorCat V I) := LaxMonoid.monObj d S L
  exact rightModObj d S L R t hu ha

example : letI := ColimitMonoidal.monoidalCategory d
    letI := LaxMonoid.monObj d S L
    (rightModObj d S L R t hu ha).smul = descend d S R t := rightModObj_action d S L R t hu ha

example : letI := ColimitMonoidal.monoidalCategory d
    letI := LaxMonoid.monObj d S L
    (rightModule d S L R t hu ha).action = descend d S R t := rightModule_action d S L R t hu ha

example : letI := ColimitMonoidal.monoidalCategory d
    letI := LaxMonoid.monObj d S L
    external d S (rightModule d S L R t hu ha).X (rightModule d S L R t hu ha).action = t :=
  rightModule_external d S L R t hu ha

example (n j : I) : letI := ColimitMonoidal.monoidalCategory d
    letI := LaxMonoid.monObj d S L
    sigma d S (rightModule d S L R t hu ha).X (rightModule d S L R t hu ha).action n j =
      (eHomEquiv V).symm (t.app (n, j)) := rightModule_sigma d S L R t hu ha n j

end Converse

/-- The exact source unit equation is derived for every actual stock right module. -/
theorem stock_unit :
    letI := ColimitMonoidal.monoidalCategory d
    letI := LaxMonoid.monObj d S L
    ∀ (M : CommutativeModuleConversion.RightModule (⟨S⟩ : EnrichedFunctorCat V I)) (n : I),
      (M.X.toEnrichedFunctor.obj n ◁ L.epsilon) ≫
        (eHomEquiv V).symm ((external d S M.X M.action).app (n, 𝟙_ I)) ≫
        M.X.toEnrichedFunctor.toOrdinaryFunctor.map (ρ_ n).hom = (ρ_ (M.X.toEnrichedFunctor.obj n)).hom :=
  stock_external_unit d S L

/-- The exact source associativity equation is derived for every actual stock right module. -/
theorem stock_assoc :
    letI := ColimitMonoidal.monoidalCategory d
    letI := LaxMonoid.monObj d S L
    ∀ (M : CommutativeModuleConversion.RightModule (⟨S⟩ : EnrichedFunctorCat V I)) (n j b : I),
      (α_ (M.X.toEnrichedFunctor.obj n) (S.obj j) (S.obj b)).inv ≫
        ((eHomEquiv V).symm ((external d S M.X M.action).app (n, j)) ▷ S.obj b) ≫
        (eHomEquiv V).symm ((external d S M.X M.action).app (n ⊗ j, b)) =
      (M.X.toEnrichedFunctor.obj n ◁ L.mu j b) ≫
        (eHomEquiv V).symm ((external d S M.X M.action).app (n, j ⊗ b)) ≫
        M.X.toEnrichedFunctor.toOrdinaryFunctor.map (α_ n j b).inv := stock_external_assoc d S L

example : letI := ColimitMonoidal.monoidalCategory d
    letI := LaxMonoid.monObj d S L
    ∀ M : CommutativeModuleConversion.RightModule (⟨S⟩ : EnrichedFunctorCat V I),
      (moduleEquiv d S L).symm ((moduleEquiv d S L) M) = M := (moduleEquiv d S L).left_inv

example : letI := ColimitMonoidal.monoidalCategory d
    letI := LaxMonoid.monObj d S L
    ∀ P : SourceModule d S L, (moduleEquiv d S L) ((moduleEquiv d S L).symm P) = P :=
  (moduleEquiv d S L).right_inv

example : letI := ColimitMonoidal.monoidalCategory d
    letI := LaxMonoid.monObj d S L
    ∀ (M N : CommutativeModuleConversion.RightModule (⟨S⟩ : EnrichedFunctorCat V I)) (f : M ⟶ N),
      (homEquiv d S L M N).symm ((homEquiv d S L M N) f) = f := by
  intro M N f
  exact (homEquiv d S L M N).left_inv f

example : letI := ColimitMonoidal.monoidalCategory d
    letI := LaxMonoid.monObj d S L
    ∀ M : CommutativeModuleConversion.RightModule (⟨S⟩ : EnrichedFunctorCat V I),
      homOfSourceComm d S L (𝟙 M.X) (source_comm_id d S L M) = 𝟙 M := homOfSourceComm_id d S L

example : letI := ColimitMonoidal.monoidalCategory d
    letI := LaxMonoid.monObj d S L
    ∀ {M N P : CommutativeModuleConversion.RightModule (⟨S⟩ : EnrichedFunctorCat V I)}
      (f : M.X ⟶ N.X) (g : N.X ⟶ P.X)
      (hf : SourceComm d S M.X N.X M.action N.action f)
      (hg : SourceComm d S N.X P.X N.action P.action g),
      homOfSourceComm d S L (f ≫ g) (source_comm_comp d S L f g hf hg) =
        homOfSourceComm d S L f hf ≫ homOfSourceComm d S L g hg := homOfSourceComm_comp d S L

example (R R' : EnrichedFunctorCat V I) (t : Transformation d S R) (t' : Transformation d S R')
    (hu : SourceUnitLaw d S L R t) (ha : SourceAssocLaw d S L R t)
    (hu' : SourceUnitLaw d S L R' t') (ha' : SourceAssocLaw d S L R' t')
    (f : R ⟶ R')
    (hf : ∀ n j : I, (eHomEquiv V).symm (t.app (n, j)) ≫ component f (n ⊗ j) =
      (component f n ⊗ₘ 𝟙 (S.obj j)) ≫ (eHomEquiv V).symm (t'.app (n, j))) :
    letI := ColimitMonoidal.monoidalCategory d
    letI := LaxMonoid.monObj d S L
    (homOfTransformation d S L R R' t t' hu ha hu' ha' f hf).hom = f :=
  homOfTransformation_hom d S L R R' t t' hu ha hu' ha' f hf

end MathlibExtTest.ExternalRightModule

run_cmd do
  let env ← Lean.getEnv
  let constructor := `CategoryTheory.EnrichedDayKernel.ExternalRightModule.rightModObj
  if Lean.Meta.isInstanceCore env constructor then
    throwError "The law-dependent rightModObj constructor is registered as an instance."
  unless Lean.getReducibilityStatusCore env constructor == .semireducible do
    throwError "The rightModObj constructor is not an ordinary semireducible definition."
  Lean.logInfo "RIGHT_MOD_OBJ_ORDINARY_DEFINITION_NO_GLOBAL_INSTANCE"
  for producer in #[`MathlibExt.CategoryTheory.Enriched.Monoidal.DayConvolution.ExternalRightModule,
      `MathlibExt.CategoryTheory.Enriched.Monoidal.DayConvolution.ExternalRightModuleCorrespondence] do
    let some idx := env.getModuleIdx? producer | throwError "producer module absent: {producer}"
    let mut count : Nat := 0
    for (name, ci) in env.constants do
      if env.getModuleIdxFor? name == some idx then
        if ci.isUnsafe then throwError "unsafe producer declaration: {name}"
        let axioms ← Lean.collectAxioms name
        for ax in axioms do
          unless ax == `propext || ax == `Classical.choice || ax == `Quot.sound do
            throwError "nonstandard axiom at {name}: {ax}"
        Lean.logInfo m!"PRODUCER_STD3 {name} {axioms}"
        count := count + 1
    unless count > 0 do throwError "zero producer declarations: {producer}"
    Lean.logInfo m!"PRODUCER_COUNT {producer} {count}"

#lint only unusedArguments in MathlibExt.CategoryTheory.Enriched.Monoidal.DayConvolution.ExternalRightModule
#lint only unusedArguments in MathlibExt.CategoryTheory.Enriched.Monoidal.DayConvolution.ExternalRightModuleCorrespondence
