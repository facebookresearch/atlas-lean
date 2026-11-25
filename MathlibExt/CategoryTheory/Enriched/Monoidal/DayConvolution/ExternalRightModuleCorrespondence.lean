/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.CategoryTheory.Enriched.Monoidal.DayConvolution.ExternalRightModule

/-!
# The source-action and stock right-module correspondence for Day convolution

A genuine external transformation satisfying the literal MMSS unit and
associativity equations descends to the original stock right-module action.
The extraction and descent are inverse on whole actions. The original Day
action square and the source square on every index pair give the same module
morphisms.

## Source and scope

Michael A. Mandell, J. Peter May, Stefan Schwede, and Brooke Shipley,
*Model Categories of Diagram Spectra*, Proceedings of the London Mathematical
Society (3) 82 (2001), no. 2, 441–512. The locators here use the December 30,
1999 preprint: Definition 1.9 (page 8) specifies the external action and its
unit and associativity diagrams; Proposition 1.10 (page 9) identifies these
actions with internal right modules. Definition 21.4 and the left Kan extension
universal property (21.5) (page 60) give the descent, and Proposition 22.1 and
the following paragraph (page 61) express the monoid and action in terms of a
lax monoidal functor.

This file proves that action correspondence for enriched Day convolution in
the arbitrary ambient and index categories `V` and `I` under the hypotheses
below. The monoid called `R` in MMSS is `S` here, with lax monoidal structure
`L`; its module diagram is called `R` here. `moduleEquiv` is a bijection on
complete source-lawful action data, and `homEquiv` identifies the corresponding
original module morphisms. The native `D_R` construction of Construction 2.1
and Theorem 2.2 (page 9), its sphere-index specialization `I_S`, and the enriched
`Map_R` mapping-object construction require separate native specializations.
In particular, the internal function object uses the equalizer (22.3)
(page 61), beyond the object and morphism correspondence proved here.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 512
noncomputable section
universe uV vV uI vI

open CategoryTheory Limits MonoidalCategory BraidedCategory MonoidalOpposite
open scoped MonoidalClosed CategoryTheory.MonObj

namespace CategoryTheory.EnrichedDayKernel.ExternalRightModule

open EnrichedFunctorCat
attribute [local instance] Enriched.prodCategory ColimitMonoidal.smallestColimits
attribute [local instance] MonoidalLeftAction.monoidalOppositeLeftAction

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [SymmetricCategory V] [MonoidalClosed V]
  {I : Type uI} [Category.{vI} I] [MonoidalCategory I]
  [EnrichedOrdinaryCategory V I] [HasColimitsOfSize.{uI, uI} V]
  (d : EnrichedMonoidalCategoryData V I) (S : EnrichedFunctor V I V)
  (L : EnrichedFunctor.LaxMonoidalData d (MonoidalClosed.enrichedMonoidalCategoryDataSelf V) S)

/-- The genuine external action transformation, with its full enriched naturality. -/
abbrev Transformation (R : EnrichedFunctorCat V I) :=
  GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V))
    (R.toEnrichedFunctor.externalTensor S) (d.tensorEnrichedFunctor.comp V R.toEnrichedFunctor)

/-- Extraction and actual Day descent are inverse on the complete action data. -/
def actionEquiv (R : EnrichedFunctorCat V I) : Action d S R ≃ Transformation d S R where
  toFun := external d S R
  invFun := descend d S R
  left_inv := descend_external d S R
  right_inv := external_descend d S R

/-- The literal MMSS unit equation on a genuine external transformation. -/
def SourceUnitLaw (R : EnrichedFunctorCat V I) (t : Transformation d S R) : Prop :=
  ∀ n : I, (R.toEnrichedFunctor.obj n ◁ L.epsilon) ≫
    (eHomEquiv V).symm (t.app (n, 𝟙_ I)) ≫
    R.toEnrichedFunctor.toOrdinaryFunctor.map (ρ_ n).hom = (ρ_ (R.toEnrichedFunctor.obj n)).hom

/-- The literal MMSS associativity equation on a genuine external transformation. -/
def SourceAssocLaw (R : EnrichedFunctorCat V I) (t : Transformation d S R) : Prop :=
  ∀ n j b : I, (α_ (R.toEnrichedFunctor.obj n) (S.obj j) (S.obj b)).inv ≫
      ((eHomEquiv V).symm (t.app (n, j)) ▷ S.obj b) ≫
      (eHomEquiv V).symm (t.app (n ⊗ j, b)) =
    (R.toEnrichedFunctor.obj n ◁ L.mu j b) ≫
      (eHomEquiv V).symm (t.app (n, j ⊗ b)) ≫
      R.toEnrichedFunctor.toOrdinaryFunctor.map (α_ n j b).inv

/-- Descent retains the exact source unit equation. -/
theorem source_unit_iff (R : EnrichedFunctorCat V I) (t : Transformation d S R) :
    SourceUnitLaw d S L R t ↔ UnitLaw d S L R (descend d S R t) := by
  simp only [SourceUnitLaw, UnitLaw, sigma_descend]
  rfl

/-- Descent retains the exact source associativity equation. -/
theorem source_assoc_iff (R : EnrichedFunctorCat V I) (t : Transformation d S R) :
    SourceAssocLaw d S L R t ↔ AssocLaw d S L R (descend d S R t) := by
  simp only [SourceAssocLaw, AssocLaw, sigma_descend]
  rfl

-- The action and its laws are explicit choices absent from the class output.
set_option warn.classDefReducibility false in
/-- Primitive MMSS source laws construct the actual stock module structure. -/
def rightModObj (R : EnrichedFunctorCat V I) (t : Transformation d S R)
    (hu : SourceUnitLaw d S L R t) (ha : SourceAssocLaw d S L R t) :
    letI := ColimitMonoidal.monoidalCategory d
    letI := LaxMonoid.monObj d S L
    ModObj (mop (⟨S⟩ : EnrichedFunctorCat V I)) R := by
  let : MonoidalCategory (EnrichedFunctorCat V I) := ColimitMonoidal.monoidalCategory d
  let : MonObj (⟨S⟩ : EnrichedFunctorCat V I) := LaxMonoid.monObj d S L
  refine { smul := descend d S R t, one_smul := ?_, mul_smul := ?_ }
  · change (R ◁ LaxMonoid.unit d S L) ≫ descend d S R t = (ρ_ R).hom
    exact (unit_iff d S L R (descend d S R t)).1 ((source_unit_iff d S L R t).1 hu)
  · change (R ◁ LaxMonoid.multiply d S L) ≫ descend d S R t =
      (α_ R (⟨S⟩ : EnrichedFunctorCat V I) ⟨S⟩).inv ≫
        (descend d S R t ▷ (⟨S⟩ : EnrichedFunctorCat V I)) ≫ descend d S R t
    let α := α_ R (⟨S⟩ : EnrichedFunctorCat V I) ⟨S⟩
    have h := source_assoc_to_day d S L R (descend d S R t)
      ((source_assoc_iff d S L R t).1 ha)
    exact (α.inv_hom_id_assoc ((R ◁ LaxMonoid.multiply d S L) ≫ descend d S R t)).symm.trans
      (congrArg (fun r => α.inv ≫ r) h.symm)

/-- The module action is the original whole Day descent, with no presentation change. -/
theorem rightModObj_action (R : EnrichedFunctorCat V I) (t : Transformation d S R)
    (hu : SourceUnitLaw d S L R t) (ha : SourceAssocLaw d S L R t) :
    letI := ColimitMonoidal.monoidalCategory d
    letI := LaxMonoid.monObj d S L
    (rightModObj d S L R t hu ha).smul = descend d S R t := rfl

/-- Bundle the descended source action in the actual stock right-module carrier. -/
def rightModule (R : EnrichedFunctorCat V I) (t : Transformation d S R)
    (hu : SourceUnitLaw d S L R t) (ha : SourceAssocLaw d S L R t) :
    letI := ColimitMonoidal.monoidalCategory d
    letI := LaxMonoid.monObj d S L
    CommutativeModuleConversion.RightModule (⟨S⟩ : EnrichedFunctorCat V I) := by
  let : MonoidalCategory (EnrichedFunctorCat V I) := ColimitMonoidal.monoidalCategory d
  let : MonObj (⟨S⟩ : EnrichedFunctorCat V I) := LaxMonoid.monObj d S L
  exact { X := R, mod := rightModObj d S L R t hu ha }

/-- The original diagram is the literal underlying object of the constructed module. -/
theorem rightModule_X (R : EnrichedFunctorCat V I) (t : Transformation d S R)
    (hu : SourceUnitLaw d S L R t) (ha : SourceAssocLaw d S L R t) :
    letI := ColimitMonoidal.monoidalCategory d
    letI := LaxMonoid.monObj d S L
    (rightModule d S L R t hu ha).X = R := rfl

/-- The constructed stock module retains the entire original descended action. -/
theorem rightModule_action (R : EnrichedFunctorCat V I) (t : Transformation d S R)
    (hu : SourceUnitLaw d S L R t) (ha : SourceAssocLaw d S L R t) :
    letI := ColimitMonoidal.monoidalCategory d
    letI := LaxMonoid.monObj d S L
    (rightModule d S L R t hu ha).action = descend d S R t := rfl

/-- Every extracted source component of the constructed stock module is the original one. -/
theorem rightModule_sigma (R : EnrichedFunctorCat V I) (t : Transformation d S R)
    (hu : SourceUnitLaw d S L R t) (ha : SourceAssocLaw d S L R t) (n j : I) :
    letI := ColimitMonoidal.monoidalCategory d
    letI := LaxMonoid.monObj d S L
    sigma d S (rightModule d S L R t hu ha).X (rightModule d S L R t hu ha).action n j =
      (eHomEquiv V).symm (t.app (n, j)) := sigma_descend d S R t n j

/-- The complete extracted genuine transformation is recovered, including all its naturality. -/
theorem rightModule_external (R : EnrichedFunctorCat V I) (t : Transformation d S R)
    (hu : SourceUnitLaw d S L R t) (ha : SourceAssocLaw d S L R t) :
    letI := ColimitMonoidal.monoidalCategory d
    letI := LaxMonoid.monObj d S L
    external d S (rightModule d S L R t hu ha).X (rightModule d S L R t hu ha).action = t :=
  external_descend d S R t

/-- The extracted genuine stock transformation satisfies the primitive source unit law. -/
theorem stock_external_unit :
    letI := ColimitMonoidal.monoidalCategory d
    letI := LaxMonoid.monObj d S L
    ∀ M : CommutativeModuleConversion.RightModule (⟨S⟩ : EnrichedFunctorCat V I),
      SourceUnitLaw d S L M.X (external d S M.X M.action) := by
  let : MonoidalCategory (EnrichedFunctorCat V I) := ColimitMonoidal.monoidalCategory d
  let : MonObj (⟨S⟩ : EnrichedFunctorCat V I) := LaxMonoid.monObj d S L
  intro M n
  exact (congrArg (fun r => (M.X.toEnrichedFunctor.obj n ◁ L.epsilon) ≫ r ≫
    M.X.toEnrichedFunctor.toOrdinaryFunctor.map (ρ_ n).hom)
      (external_component d S M.X M.action n (𝟙_ I))).trans (stock_sigma_unit d S L M n)

/-- The extracted genuine stock transformation satisfies the primitive source associativity law. -/
theorem stock_external_assoc :
    letI := ColimitMonoidal.monoidalCategory d
    letI := LaxMonoid.monObj d S L
    ∀ M : CommutativeModuleConversion.RightModule (⟨S⟩ : EnrichedFunctorCat V I),
      SourceAssocLaw d S L M.X (external d S M.X M.action) := by
  let : MonoidalCategory (EnrichedFunctorCat V I) := ColimitMonoidal.monoidalCategory d
  let : MonObj (⟨S⟩ : EnrichedFunctorCat V I) := LaxMonoid.monObj d S L
  intro M n j b
  have hl := congrArg₂ (fun r s => (α_ (M.X.toEnrichedFunctor.obj n) (S.obj j) (S.obj b)).inv ≫
    (r ▷ S.obj b) ≫ s)
      (external_component d S M.X M.action n j) (external_component d S M.X M.action (n ⊗ j) b)
  have hr := congrArg (fun r => (M.X.toEnrichedFunctor.obj n ◁ L.mu j b) ≫ r ≫
    M.X.toEnrichedFunctor.toOrdinaryFunctor.map (α_ n j b).inv)
      (external_component d S M.X M.action n (j ⊗ b))
  exact hl.trans ((stock_sigma_assoc d S L M n j b).trans hr.symm)

/-- Reconstructing a stock module recovers its literal original action. -/
theorem rightModule_stock_action :
    letI := ColimitMonoidal.monoidalCategory d
    letI := LaxMonoid.monObj d S L
    ∀ M : CommutativeModuleConversion.RightModule (⟨S⟩ : EnrichedFunctorCat V I),
      (rightModule d S L M.X (external d S M.X M.action)
        (stock_external_unit d S L M) (stock_external_assoc d S L M)).action = M.action := by
  let : MonoidalCategory (EnrichedFunctorCat V I) := ColimitMonoidal.monoidalCategory d
  let : MonObj (⟨S⟩ : EnrichedFunctorCat V I) := LaxMonoid.monObj d S L
  intro M
  exact descend_external d S M.X M.action

/-- Extracting and reconstructing a stock module recovers the original bundled object. -/
theorem rightModule_stock :
    letI := ColimitMonoidal.monoidalCategory d
    letI := LaxMonoid.monObj d S L
    ∀ M : CommutativeModuleConversion.RightModule (⟨S⟩ : EnrichedFunctorCat V I),
      rightModule d S L M.X (external d S M.X M.action)
        (stock_external_unit d S L M) (stock_external_assoc d S L M) = M := by
  let : MonoidalCategory (EnrichedFunctorCat V I) := ColimitMonoidal.monoidalCategory d
  let : MonObj (⟨S⟩ : EnrichedFunctorCat V I) := LaxMonoid.monObj d S L
  intro M
  cases M with
  | @mk R m =>
    let p := rightModObj d S L R (external d S R m.smul)
      (stock_external_unit d S L { X := R, mod := m })
          (stock_external_assoc d S L { X := R, mod := m })
    have hp : p.smul = m.smul := descend_external d S R m.smul
    have hm : p = m := by
      have hext : ∀ q q' : ModObj (mop (⟨S⟩ : EnrichedFunctorCat V I)) R,
          q.smul = q'.smul → q = q' := by
        intro q q' h
        cases q
        cases q'
        cases h
        rfl
      exact hext p m hp
    exact congrArg
        (fun q =>
          ({ X := R, mod := q } : CommutativeModuleConversion.RightModule
            (⟨S⟩ : EnrichedFunctorCat V I))) hm

/-- Actual source diagrams with genuine external actions and the two primitive MMSS laws. -/
abbrev SourceModule := Σ R : EnrichedFunctorCat V I,
  { t : Transformation d S R // SourceUnitLaw d S L R t ∧ SourceAssocLaw d S L R t }

/-- Whole stock modules and source-lawful genuine external actions are in bijection. -/
def moduleEquiv :
    letI := ColimitMonoidal.monoidalCategory d
    letI := LaxMonoid.monObj d S L
    CommutativeModuleConversion.RightModule (⟨S⟩ : EnrichedFunctorCat V I) ≃
        SourceModule d S L := by
  let : MonoidalCategory (EnrichedFunctorCat V I) := ColimitMonoidal.monoidalCategory d
  let : MonObj (⟨S⟩ : EnrichedFunctorCat V I) := LaxMonoid.monObj d S L
  exact {
    toFun := fun M => ⟨M.X,
        ⟨external d S M.X M.action,
          stock_external_unit d S L M, stock_external_assoc d S L M⟩⟩
    invFun := fun P => rightModule d S L P.1 P.2.val P.2.property.1 P.2.property.2
    left_inv := rightModule_stock d S L
    right_inv := fun P => by
      rcases P with ⟨R, t, hu, ha⟩
      apply congrArg (fun q => (⟨R, q⟩ : SourceModule d S L))
      exact Subtype.ext (rightModule_external d S L R t hu ha) }

/-- The external morphism equation on every whole index-pair coefficient object. -/
def SourceComm (R R' : EnrichedFunctorCat V I) (a : Action d S R) (b : Action d S R')
    (f : R ⟶ R') : Prop :=
  ∀ n j : I, sigma d S R a n j ≫ component f (n ⊗ j) =
    (component f n ⊗ₘ 𝟙 (S.obj j)) ≫ sigma d S R' b n j

/-- Original input naturality retains the entire identity-weight generator square. -/
theorem point_input_action (R R' : EnrichedFunctorCat V I) (f : R ⟶ R') (b : Action d S R')
    (n j : I) :
    Generators.point d.tensorEnrichedFunctor R.toEnrichedFunctor S (n, j) ≫
        component (Input.natTrans d.tensorEnrichedFunctor f (GradedNatTrans.unitId S) ≫ b) (n ⊗ j) =
      (component f n ⊗ₘ 𝟙 (S.obj j)) ≫ sigma d S R' b n j := by
  let pnt := Generators.point d.tensorEnrichedFunctor R.toEnrichedFunctor S (n, j)
  let pnt' := Generators.point d.tensorEnrichedFunctor R'.toEnrichedFunctor S (n, j)
  let m := Input.natTrans d.tensorEnrichedFunctor f (GradedNatTrans.unitId S)
  let q := component b (n ⊗ j)
  let p := component f n ⊗ₘ 𝟙 (S.obj j)
  have hm : component m (n ⊗ j) = Input.mapAt d.tensorEnrichedFunctor f
      (GradedNatTrans.unitId S) (n ⊗ j) :=
    Input.natTrans_component d.tensorEnrichedFunctor f (GradedNatTrans.unitId S) (n ⊗ j)
  have hp : pnt ≫ component m (n ⊗ j) = p ≫ pnt' :=
    (congrArg (fun r => pnt ≫ r) hm).trans
      ((Generators.point_input_natural d.tensorEnrichedFunctor f (GradedNatTrans.unitId S)
          (n, j)).trans
        (congrArg (fun r => (component f n ⊗ₘ r) ≫ pnt') (GradedNatTrans.unitId_component S j)))
  exact (congrArg (fun r => pnt ≫ r) (component_comp m b (n ⊗ j))).trans
    ((Category.assoc pnt (component m (n ⊗ j)) q).symm.trans
      ((congrArg (fun r => r ≫ q) hp).trans (Category.assoc p pnt' q)))

/-- Postcomposition retains the literal full external action component. -/
theorem point_action_comp (R R' : EnrichedFunctorCat V I) (a : Action d S R)
    (f : R ⟶ R') (n j : I) :
    Generators.point d.tensorEnrichedFunctor R.toEnrichedFunctor S (n, j) ≫
        component (a ≫ f) (n ⊗ j) = sigma d S R a n j ≫ component f (n ⊗ j) :=
  (congrArg (fun r => Generators.point d.tensorEnrichedFunctor R.toEnrichedFunctor S (n, j) ≫ r)
    (component_comp a f (n ⊗ j))).trans (Category.assoc _ _ _).symm

/-- Every original full output-Hom generator retains the complete postcomposition action. -/
theorem gen_action_comp (R R' : EnrichedFunctorCat V I) (a : Action d S R)
    (f : R ⟶ R') (k n j : I) :
    gen d.tensorEnrichedFunctor R.toEnrichedFunctor S k (n, j) ≫ component (a ≫ f) k =
      (𝟙 ((n ⊗ j) ⟶[V] k) ⊗ₘ (sigma d S R a n j ≫ component f (n ⊗ j))) ≫
        ActionFromTransformation.targetAction R'.toEnrichedFunctor (n ⊗ j) k := by
  let t := ActionFromTransformation.extract d.tensorEnrichedFunctor R.toEnrichedFunctor S
      R'.toEnrichedFunctor (a ≫ f)
  have hc : ActionFromTransformation.component d.tensorEnrichedFunctor R.toEnrichedFunctor S
      R'.toEnrichedFunctor t (n, j) =
      sigma d S R a n j ≫ component f (n ⊗ j) :=
    (ActionFromTransformation.extract_component _ _ _ _ _ _).trans
        (point_action_comp d S R R' a f n j)
  exact (ActionFromTransformation.gen_extract _ _ _ _ (a ≫ f) k (n, j)).symm.trans
    ((ActionFromTransformation.generator_eq _ _ _ _ t k (n, j)).trans
      ((congrArg (fun r => (((n ⊗ j) ⟶[V] k) ◁ r) ≫
        ActionFromTransformation.targetAction R'.toEnrichedFunctor (n ⊗ j) k) hc).trans
          (congrArg
              (fun r => r ≫ ActionFromTransformation.targetAction
                R'.toEnrichedFunctor (n ⊗ j) k)
            (id_tensorHom ((n ⊗ j) ⟶[V] k) (sigma d S R a n j ≫ component f (n ⊗ j))).symm)))

/-- Every original full output-Hom generator retains the complete input action. -/
theorem gen_input_action (R R' : EnrichedFunctorCat V I) (f : R ⟶ R') (b : Action d S R')
    (k n j : I) :
    gen d.tensorEnrichedFunctor R.toEnrichedFunctor S k (n, j) ≫
        component (Input.natTrans d.tensorEnrichedFunctor f (GradedNatTrans.unitId S) ≫ b) k =
      (𝟙 ((n ⊗ j) ⟶[V] k) ⊗ₘ ((component f n ⊗ₘ 𝟙 (S.obj j)) ≫ sigma d S R' b n j)) ≫
        ActionFromTransformation.targetAction R'.toEnrichedFunctor (n ⊗ j) k := by
  let m := Input.natTrans d.tensorEnrichedFunctor f (GradedNatTrans.unitId S) ≫ b
  let t := ActionFromTransformation.extract d.tensorEnrichedFunctor R.toEnrichedFunctor S
      R'.toEnrichedFunctor m
  have hc : ActionFromTransformation.component d.tensorEnrichedFunctor R.toEnrichedFunctor S
      R'.toEnrichedFunctor t (n, j) =
      (component f n ⊗ₘ 𝟙 (S.obj j)) ≫ sigma d S R' b n j :=
    (ActionFromTransformation.extract_component _ _ _ _ _ _).trans
        (point_input_action d S R R' f b n j)
  exact (ActionFromTransformation.gen_extract _ _ _ _ m k (n, j)).symm.trans
    ((ActionFromTransformation.generator_eq _ _ _ _ t k (n, j)).trans
      ((congrArg (fun r => (((n ⊗ j) ⟶[V] k) ◁ r) ≫
        ActionFromTransformation.targetAction R'.toEnrichedFunctor (n ⊗ j) k) hc).trans
          (congrArg
              (fun r => r ≫ ActionFromTransformation.targetAction
                R'.toEnrichedFunctor (n ⊗ j) k)
            (id_tensorHom ((n ⊗ j) ⟶[V] k)
                ((component f n ⊗ₘ 𝟙 (S.obj j)) ≫ sigma d S R' b n j)).symm)))

/-- The source square is equivalent to the complete original Day action square. -/
theorem comm_iff (R R' : EnrichedFunctorCat V I) (a : Action d S R) (b : Action d S R')
    (f : R ⟶ R') :
    SourceComm d S R R' a b f ↔
      a ≫ f = Input.natTrans d.tensorEnrichedFunctor f (GradedNatTrans.unitId S) ≫ b := by
  constructor
  · intro h
    apply EnrichedFunctorCat.hom_ext
    intro k
    apply EnrichedDayKernel.hom_ext d.tensorEnrichedFunctor R.toEnrichedFunctor S k
    intro x
    exact (gen_action_comp d S R R' a f k x.1 x.2).trans
      ((congrArg (fun r => (𝟙 ((x.1 ⊗ x.2) ⟶[V] k) ⊗ₘ r) ≫
        ActionFromTransformation.targetAction R'.toEnrichedFunctor (x.1 ⊗ x.2) k) (h x.1 x.2)).trans
          (gen_input_action d S R R' f b k x.1 x.2).symm)
  · intro h n j
    exact (point_action_comp d S R R' a f n j).symm.trans
      ((congrArg (fun r => Generators.point d.tensorEnrichedFunctor R.toEnrichedFunctor S (n, j) ≫
        component r (n ⊗ j)) h).trans (point_input_action d S R R' f b n j))

/-- Every stock module morphism preserves the whole external action on each index pair. -/
theorem stock_source_comm :
    letI := ColimitMonoidal.monoidalCategory d
    letI := LaxMonoid.monObj d S L
    ∀ {M N : CommutativeModuleConversion.RightModule (⟨S⟩ : EnrichedFunctorCat V I)} (f : M ⟶ N),
      SourceComm d S M.X N.X M.action N.action f.hom := by
  let : MonoidalCategory (EnrichedFunctorCat V I) := ColimitMonoidal.monoidalCategory d
  let : MonObj (⟨S⟩ : EnrichedFunctorCat V I) := LaxMonoid.monObj d S L
  intro M N f
  exact (comm_iff d S M.X N.X M.action N.action f.hom).2
    (CommutativeModuleConversion.RightModule.comm f)

/-- A source-preserving original diagram map is an actual stock module morphism. -/
def homOfSourceComm :
    letI := ColimitMonoidal.monoidalCategory d
    letI := LaxMonoid.monObj d S L
    ∀ {M N : CommutativeModuleConversion.RightModule (⟨S⟩ : EnrichedFunctorCat V I)}
        (f : M.X ⟶ N.X),
      SourceComm d S M.X N.X M.action N.action f → (M ⟶ N) := by
  let : MonoidalCategory (EnrichedFunctorCat V I) := ColimitMonoidal.monoidalCategory d
  let : MonObj (⟨S⟩ : EnrichedFunctorCat V I) := LaxMonoid.monObj d S L
  intro M N f h
  exact Mod.Hom.mk' f ((comm_iff d S M.X N.X M.action N.action f).1 h)

/-- The constructed stock morphism is the literal original diagram map. -/
theorem homOfSourceComm_hom :
    letI := ColimitMonoidal.monoidalCategory d
    letI := LaxMonoid.monObj d S L
    ∀ {M N : CommutativeModuleConversion.RightModule (⟨S⟩ : EnrichedFunctorCat V I)} (f : M.X ⟶ N.X)
      (h : SourceComm d S M.X N.X M.action N.action f),
      (homOfSourceComm d S L f h).hom = f := by
  intro M N f h
  rfl

/-- Stock module morphisms and all source-preserving original maps are in bijection. -/
def homEquiv :
    letI := ColimitMonoidal.monoidalCategory d
    letI := LaxMonoid.monObj d S L
    ∀ M N : CommutativeModuleConversion.RightModule (⟨S⟩ : EnrichedFunctorCat V I),
      (M ⟶ N) ≃ { f : M.X ⟶ N.X // SourceComm d S M.X N.X M.action N.action f } := by
  let : MonoidalCategory (EnrichedFunctorCat V I) := ColimitMonoidal.monoidalCategory d
  let : MonObj (⟨S⟩ : EnrichedFunctorCat V I) := LaxMonoid.monObj d S L
  intro M N
  exact {
    toFun := fun f => ⟨f.hom, stock_source_comm d S L f⟩
    invFun := fun f => homOfSourceComm d S L f.val f.property
    left_inv := fun f => Mod.Hom.ext rfl
    right_inv := fun f => Subtype.ext rfl }

/-- Every original identity map preserves the source external action. -/
theorem source_comm_id :
    letI := ColimitMonoidal.monoidalCategory d
    letI := LaxMonoid.monObj d S L
    ∀ M : CommutativeModuleConversion.RightModule (⟨S⟩ : EnrichedFunctorCat V I),
      SourceComm d S M.X M.X M.action M.action (𝟙 M.X) := by
  let : MonoidalCategory (EnrichedFunctorCat V I) := ColimitMonoidal.monoidalCategory d
  let : MonObj (⟨S⟩ : EnrichedFunctorCat V I) := LaxMonoid.monObj d S L
  intro M
  exact stock_source_comm d S L (𝟙 M)

/-- Original composition preserves the complete source square. -/
theorem source_comm_comp :
    letI := ColimitMonoidal.monoidalCategory d
    letI := LaxMonoid.monObj d S L
    ∀ {M N P : CommutativeModuleConversion.RightModule (⟨S⟩ : EnrichedFunctorCat V I)}
      (f : M.X ⟶ N.X) (g : N.X ⟶ P.X),
      SourceComm d S M.X N.X M.action N.action f →
      SourceComm d S N.X P.X N.action P.action g →
      SourceComm d S M.X P.X M.action P.action (f ≫ g) := by
  let : MonoidalCategory (EnrichedFunctorCat V I) := ColimitMonoidal.monoidalCategory d
  let : MonObj (⟨S⟩ : EnrichedFunctorCat V I) := LaxMonoid.monObj d S L
  intro M N P f g hf hg
  exact stock_source_comm d S L (homOfSourceComm d S L f hf ≫ homOfSourceComm d S L g hg)

/-- The source-to-stock morphism construction preserves the original identity. -/
theorem homOfSourceComm_id :
    letI := ColimitMonoidal.monoidalCategory d
    letI := LaxMonoid.monObj d S L
    ∀ M : CommutativeModuleConversion.RightModule (⟨S⟩ : EnrichedFunctorCat V I),
      homOfSourceComm d S L (𝟙 M.X) (source_comm_id d S L M) = 𝟙 M := by
  intro M
  exact Mod.Hom.ext rfl

/-- The source-to-stock morphism construction preserves the original composition. -/
theorem homOfSourceComm_comp :
    letI := ColimitMonoidal.monoidalCategory d
    letI := LaxMonoid.monObj d S L
    ∀ {M N P : CommutativeModuleConversion.RightModule (⟨S⟩ : EnrichedFunctorCat V I)}
      (f : M.X ⟶ N.X) (g : N.X ⟶ P.X)
      (hf : SourceComm d S M.X N.X M.action N.action f)
      (hg : SourceComm d S N.X P.X N.action P.action g),
      homOfSourceComm d S L (f ≫ g) (source_comm_comp d S L f g hf hg) =
        homOfSourceComm d S L f hf ≫ homOfSourceComm d S L g hg := by
  intro M N P f g hf hg
  exact Mod.Hom.ext rfl

/-- The primitive MMSS morphism equation for two genuine external transformations. -/
def TransformationComm (R R' : EnrichedFunctorCat V I)
    (t : Transformation d S R) (t' : Transformation d S R') (f : R ⟶ R') : Prop :=
  ∀ n j : I, (eHomEquiv V).symm (t.app (n, j)) ≫ component f (n ⊗ j) =
    (component f n ⊗ₘ 𝟙 (S.obj j)) ≫ (eHomEquiv V).symm (t'.app (n, j))

/-- Genuine transformation morphisms retain their whole source square after descent. -/
theorem transformation_comm_iff (R R' : EnrichedFunctorCat V I)
    (t : Transformation d S R) (t' : Transformation d S R') (f : R ⟶ R') :
    TransformationComm d S R R' t t' f ↔
      SourceComm d S R R' (descend d S R t) (descend d S R' t') f := by
  simp only [TransformationComm, SourceComm, sigma_descend]
  rfl

/-- A genuine source morphism descends to a stock morphism between the actual constructed
modules. -/
def homOfTransformation (R R' : EnrichedFunctorCat V I)
    (t : Transformation d S R) (t' : Transformation d S R')
    (hu : SourceUnitLaw d S L R t) (ha : SourceAssocLaw d S L R t)
    (hu' : SourceUnitLaw d S L R' t') (ha' : SourceAssocLaw d S L R' t')
    (f : R ⟶ R') (hf : TransformationComm d S R R' t t' f) :
    letI := ColimitMonoidal.monoidalCategory d
    letI := LaxMonoid.monObj d S L
    rightModule d S L R t hu ha ⟶ rightModule d S L R' t' hu' ha' := by
  let : MonoidalCategory (EnrichedFunctorCat V I) := ColimitMonoidal.monoidalCategory d
  let : MonObj (⟨S⟩ : EnrichedFunctorCat V I) := LaxMonoid.monObj d S L
  exact homOfSourceComm d S L (M := rightModule d S L R t hu ha)
      (N := rightModule d S L R' t' hu' ha') f
    ((transformation_comm_iff d S R R' t t' f).1 hf)

/-- The descended source morphism retains its literal original enriched diagram map. -/
theorem homOfTransformation_hom (R R' : EnrichedFunctorCat V I)
    (t : Transformation d S R) (t' : Transformation d S R')
    (hu : SourceUnitLaw d S L R t) (ha : SourceAssocLaw d S L R t)
    (hu' : SourceUnitLaw d S L R' t') (ha' : SourceAssocLaw d S L R' t')
    (f : R ⟶ R') (hf : TransformationComm d S R R' t t' f) :
    letI := ColimitMonoidal.monoidalCategory d
    letI := LaxMonoid.monObj d S L
    (homOfTransformation d S L R R' t t' hu ha hu' ha' f hf).hom = f := rfl

end CategoryTheory.EnrichedDayKernel.ExternalRightModule
