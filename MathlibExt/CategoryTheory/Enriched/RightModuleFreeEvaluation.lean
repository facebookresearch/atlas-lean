/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module
public import MathlibExt.CategoryTheory.Enriched.FreeEvaluation
public import MathlibExt.CategoryTheory.Monoidal.RightModuleFreeEvaluation
public import MathlibExt.CategoryTheory.Enriched.Monoidal.DayConvolution.LaxMonoidAssembly

/-!
# Free enriched evaluation for right Day modules

The free enriched diagram functor followed by the stock right-module free
functor is left adjoint to evaluation of the underlying enriched diagram.
The complete Hom functions use the free-diagram generator and extension,
the monoid unit and the module action. Both triangle identities and arbitrary
coefficient maps are retained. The Day specialization uses only enriched
monoidal index data and a lax monoidal coefficient functor.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section

open CategoryTheory MonoidalCategory MonoidalOpposite
open CategoryTheory.Enriched
open scoped MonoidalClosed

namespace CategoryTheory.Enriched.RightModuleFreeEvaluation.Primitive
universe uV vV uI
open CategoryTheory.EnrichedFunctorCat
attribute [local instance] MonoidalLeftAction.monoidalOppositeLeftAction
variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V] {I : Type uI} [EnrichedCategory V I]
  [MonoidalCategory (EnrichedFunctorCat V I)]
  (S : EnrichedFunctorCat V I) [MonObj S]
/-- The original free enriched I-space followed by the actual stock right-module free functor. -/
abbrev free (n : I) : V ⥤ CommutativeModuleConversion.RightModule S :=
  Free.functor n ⋙ RightModuleFree.functor S
/-- The actual stock forgetful functor followed by original enriched I-space evaluation. -/
abbrev evaluation (n : I) : CommutativeModuleConversion.RightModule S ⥤ V :=
  Mod.forget (D := EnrichedFunctorCat V I) (mop S) ⋙ EnrichedFunctorCat.evaluation n
/-- The genuine composition of the original free/evaluation adjunctions. -/
abbrev adjunction (n : I) : free S n ⊣ evaluation S n :=
  (Free.adjunction n).comp (RightModuleFree.adjunction S)
/-- Forward evaluation for the complete original composed free adjunction. -/
def HomApplyFormula (n : I) (X : V) (M : CommutativeModuleConversion.RightModule S)
    (q : (free S n).obj X ⟶ M) : Prop :=
  (adjunction S n).homEquiv X M q =
    Free.evaluate n X M.X (RightModuleFree.freeGenerator S (Free.object n X) ≫ q.hom)

/-- The complete composed forward Hom function retains both original generator evaluations. -/
theorem hom_apply (n : I) (X : V) (M : CommutativeModuleConversion.RightModule S)
    (q : (free S n).obj X ⟶ M) : HomApplyFormula S n X M q := by
  let a := Free.adjunction (V := V) n
  let b := RightModuleFree.adjunction S
  let p := RightModuleFree.freeGenerator S (Free.object n X) ≫ q.hom
  have h := congrFun (RightModuleFree.freeHomEquiv_toFun S (Free.object n X) M) q
  have he := congrFun (congrFun (Adjunction.comp_homEquiv a b) X) M
  have hc := congrArg (fun e => e q) he
  have heFree := congrFun (congrFun (Free.adjunction_homEquiv (V := V) n) X) M.X
  have hf := congrArg (fun e => e p) heFree
  exact hc.trans ((congrArg (a.homEquiv X M.X) h).trans hf)
/-- The complete composed inverse Hom function retains the full free extension and right action. -/
theorem hom_symm_hom (n : I) (X : V) (M : CommutativeModuleConversion.RightModule S)
    (f : X ⟶ M.X.toEnrichedFunctor.obj n) :
    (((adjunction S n).homEquiv X M).symm f).hom =
      (Free.extend n X M.X f ▷ S) ≫ M.action := by
  let a := Free.adjunction (V := V) n
  let b := RightModuleFree.adjunction S
  have he := congrFun (congrFun (Adjunction.comp_homEquiv a b) X) M
  have hc := congrArg (fun e => e.symm f) he
  have heFree := congrFun (congrFun (Free.adjunction_homEquiv (V := V) n) X) M.X
  have hf := congrArg (fun e => e.symm f) heFree
  have hh := congrFun (RightModuleFree.extendFree_hom S (Free.object n X) M)
    ((a.homEquiv X M.X).symm f)
  exact (congrArg Mod.Hom.hom hc).trans
    (hh.trans (congrArg (fun g => (g ▷ S) ≫ M.action) hf))
/-- The original stock unit insertion into the complete free enriched right module. -/
def generator (n : I) (X : V) : Free.object n X ⟶ ((free S n).obj X).X :=
  RightModuleFree.freeGenerator S (Free.object n X)
/-- The original enriched free extension followed by the complete target right action. -/
def extension (n : I) (X : V) (M : CommutativeModuleConversion.RightModule S)
    (f : X ⟶ M.X.toEnrichedFunctor.obj n) : ((free S n).obj X).X ⟶ M.X :=
  (Free.extend n X M.X f ▷ S) ≫ M.action

theorem hom_apply_generator (n : I) (X : V) (M : CommutativeModuleConversion.RightModule S)
    (q : (free S n).obj X ⟶ M) :
    (adjunction S n).homEquiv X M q = Free.evaluate n X M.X (generator S n X ≫ q.hom) :=
  hom_apply S n X M q

theorem hom_symm_carrier (n : I) (X : V) (M : CommutativeModuleConversion.RightModule S)
    (f : X ⟶ M.X.toEnrichedFunctor.obj n) :
    (((adjunction S n).homEquiv X M).symm f).hom = extension S n X M f :=
  hom_symm_hom S n X M f

theorem hom_left_inv (n : I) (X : V) (M : CommutativeModuleConversion.RightModule S)
    (q : (free S n).obj X ⟶ M) :
    ((adjunction S n).homEquiv X M).symm ((adjunction S n).homEquiv X M q) = q :=
  ((adjunction S n).homEquiv X M).symm_apply_apply q

theorem hom_right_inv (n : I) (X : V) (M : CommutativeModuleConversion.RightModule S)
    (f : X ⟶ M.X.toEnrichedFunctor.obj n) :
    (adjunction S n).homEquiv X M (((adjunction S n).homEquiv X M).symm f) = f :=
  ((adjunction S n).homEquiv X M).apply_symm_apply f

theorem hom_extend_precompose (n : I) {X Y : V} (f : X ⟶ Y)
    (M : CommutativeModuleConversion.RightModule S) (g : Y ⟶ M.X.toEnrichedFunctor.obj n) :
    ((adjunction S n).homEquiv X M).symm (f ≫ g) =
      (free S n).map f ≫ ((adjunction S n).homEquiv Y M).symm g :=
  (adjunction S n).homEquiv_naturality_left_symm f g

theorem unit_evaluation (n : I) (X : V) :
    (adjunction S n).unit.app X =
      (adjunction S n).homEquiv X ((free S n).obj X) (𝟙 _) :=
  ((adjunction S n).homEquiv_id X).symm

/-- The complete counit extension formula for the original composed adjunction. -/
def CounitExtensionFormula (n : I) (M : CommutativeModuleConversion.RightModule S) : Prop :=
  (adjunction S n).counit.app M =
    ((adjunction S n).homEquiv (M.X.toEnrichedFunctor.obj n) M).symm
      (𝟙 (M.X.toEnrichedFunctor.obj n))

theorem counit_extension (n : I) (M : CommutativeModuleConversion.RightModule S) :
    CounitExtensionFormula S n M := by
  have h := (adjunction S n).homEquiv_counit (M.X.toEnrichedFunctor.obj n) M
    (𝟙 (M.X.toEnrichedFunctor.obj n))
  exact (h.trans ((congrArg (fun q => q ≫ (adjunction S n).counit.app M)
    ((free S n).map_id (M.X.toEnrichedFunctor.obj n))).trans (Category.id_comp _))).symm

/-- The complete free triangle for the original composed adjunction. -/
def FreeTriangleFormula (n : I) (X : V) : Prop :=
  (free S n).map ((adjunction S n).unit.app X) ≫
    (adjunction S n).counit.app ((free S n).obj X) = 𝟙 ((free S n).obj X)

theorem free_triangle (n : I) (X : V) : FreeTriangleFormula S n X :=
  (adjunction S n).left_triangle_components X

theorem evaluation_triangle (n : I) (M : CommutativeModuleConversion.RightModule S) :
    (adjunction S n).unit.app ((evaluation S n).obj M) ≫
      (evaluation S n).map ((adjunction S n).counit.app M) = 𝟙 ((evaluation S n).obj M) :=
  (adjunction S n).right_triangle_components M


/-- The entire primitive generator is the actual stock unit insertion with its original type. -/
theorem generator_original (n : I) (X : V) :
    HEq (generator S n X) (RightModuleFree.freeGenerator S (Free.object n X)) := by
  rfl

end CategoryTheory.Enriched.RightModuleFreeEvaluation.Primitive

namespace CategoryTheory.Enriched.RightModuleFreeEvaluation

universe uV vV uI vI

open Limits EnrichedDayKernel CategoryTheory.EnrichedFunctorCat
attribute [local instance] MonoidalLeftAction.monoidalOppositeLeftAction

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [SymmetricCategory V] [MonoidalClosed V]
  {I : Type uI} [Category.{vI} I] [MonoidalCategory I]
  [EnrichedOrdinaryCategory V I] [HasColimitsOfSize.{uI, uI} V]
  (d : EnrichedMonoidalCategoryData V I) (S : EnrichedFunctor V I V)
  (L : EnrichedFunctor.LaxMonoidalData d
    (MonoidalClosed.enrichedMonoidalCategoryDataSelf V) S)

/-- The original free I-space followed by the actual stock right-free functor. -/
def sourceFree (n : I) :
    letI := ColimitMonoidal.monoidalCategory d
    letI := LaxMonoid.monObj d S L
    V ⥤ CommutativeModuleConversion.RightModule (⟨S⟩ : EnrichedFunctorCat V I) := by
  letI := ColimitMonoidal.monoidalCategory d
  letI := LaxMonoid.monObj d S L
  exact Primitive.free (⟨S⟩ : EnrichedFunctorCat V I) n

/-- The actual stock forgetful functor followed by the original I-space evaluation. -/
def sourceEvaluation (n : I) :
    letI := ColimitMonoidal.monoidalCategory d
    letI := LaxMonoid.monObj d S L
    CommutativeModuleConversion.RightModule (⟨S⟩ : EnrichedFunctorCat V I) ⥤ V := by
  letI := ColimitMonoidal.monoidalCategory d
  letI := LaxMonoid.monObj d S L
  exact Primitive.evaluation (⟨S⟩ : EnrichedFunctorCat V I) n

/-- The complete source adjunction is the genuine composition of the original two. -/
def sourceAdjunction (n : I) :
    letI := ColimitMonoidal.monoidalCategory d
    letI := LaxMonoid.monObj d S L
    sourceFree d S L n ⊣ sourceEvaluation d S L n := by
  letI := ColimitMonoidal.monoidalCategory d
  letI := LaxMonoid.monObj d S L
  exact Primitive.adjunction (⟨S⟩ : EnrichedFunctorCat V I) n

/-- The stock free action retains its complete original associator and monoid multiplication. -/
theorem sourceFree_action (n : I) (X : V) :
    letI := ColimitMonoidal.monoidalCategory d
    letI := LaxMonoid.monObj d S L
    ((sourceFree d S L n).obj X).action =
      (α_ (Free.object n X) (⟨S⟩ : EnrichedFunctorCat V I) ⟨S⟩).hom ≫
        (Free.object n X ◁ MonObj.mul (X := (⟨S⟩ : EnrichedFunctorCat V I))) := by
  rfl

/-- The actual source adjunction supplies both complete Hom functions. -/
def sourceHom (n : I) (X : V) :
    letI := ColimitMonoidal.monoidalCategory d
    letI := LaxMonoid.monObj d S L
    ∀ M : CommutativeModuleConversion.RightModule (⟨S⟩ : EnrichedFunctorCat V I),
      ((sourceFree d S L n).obj X ⟶ M) ≃ (X ⟶ M.X.toEnrichedFunctor.obj n) := by
  letI := ColimitMonoidal.monoidalCategory d
  letI := LaxMonoid.monObj d S L
  exact (Primitive.adjunction (⟨S⟩ : EnrichedFunctorCat V I) n).homEquiv X

/-- The complete forward function evaluates the original stock unit and I-space identity. -/
theorem sourceHom_apply (n : I) (X : V) :
    letI := ColimitMonoidal.monoidalCategory d
    letI := LaxMonoid.monObj d S L
    ∀ (M : CommutativeModuleConversion.RightModule (⟨S⟩ : EnrichedFunctorCat V I))
      (q : (sourceFree d S L n).obj X ⟶ M),
      Primitive.HomApplyFormula (⟨S⟩ : EnrichedFunctorCat V I) n X M q := by
  intro M q
  exact @Primitive.hom_apply V _ _ _ _ I _
    (ColimitMonoidal.monoidalCategory d) (⟨S⟩ : EnrichedFunctorCat V I)
    (LaxMonoid.monObj d S L) n X M q

/-- The actual free-unit insertion, typed on the unchanged constructed free carrier. -/
def sourceGenerator (n : I) (X : V) :
    letI := ColimitMonoidal.monoidalCategory d
    letI := LaxMonoid.monObj d S L
    Free.object n X ⟶ ((sourceFree d S L n).obj X).X := by
  letI := ColimitMonoidal.monoidalCategory d
  letI := LaxMonoid.monObj d S L
  exact Primitive.generator (⟨S⟩ : EnrichedFunctorCat V I) n X

/-- The whole constructed generator is the original stock unit, with all dependent types. -/
theorem sourceGenerator_original (n : I) (X : V) :
    letI := ColimitMonoidal.monoidalCategory d
    letI := LaxMonoid.monObj d S L
    HEq (sourceGenerator d S L n X)
      (RightModuleFree.freeGenerator (⟨S⟩ : EnrichedFunctorCat V I) (Free.object n X)) := by
  exact @Primitive.generator_original V _ _ _ _ I _
    (ColimitMonoidal.monoidalCategory d) (⟨S⟩ : EnrichedFunctorCat V I)
    (LaxMonoid.monObj d S L) n X

/-- The original two-stage extension, typed on the actual free carrier. -/
def sourceExtension (n : I) (X : V) :
    letI := ColimitMonoidal.monoidalCategory d
    letI := LaxMonoid.monObj d S L
    ∀ M : CommutativeModuleConversion.RightModule (⟨S⟩ : EnrichedFunctorCat V I),
      (X ⟶ M.X.toEnrichedFunctor.obj n) →
        (((sourceFree d S L n).obj X).X ⟶ M.X) := by
  letI := ColimitMonoidal.monoidalCategory d
  letI := LaxMonoid.monObj d S L
  intro M
  exact Primitive.extension (⟨S⟩ : EnrichedFunctorCat V I) n X M

/-- The extension keeps the original complete Day map and target action with their own types. -/
theorem sourceExtension_original (n : I) (X : V) :
    letI := ColimitMonoidal.monoidalCategory d
    letI := LaxMonoid.monObj d S L
    ∀ (M : CommutativeModuleConversion.RightModule (⟨S⟩ : EnrichedFunctorCat V I))
      (f : X ⟶ M.X.toEnrichedFunctor.obj n),
      HEq (sourceExtension d S L n X M f)
        ((Free.extend n X M.X f ▷ (⟨S⟩ : EnrichedFunctorCat V I)) ≫ M.action) := by
  let : MonoidalCategory (EnrichedFunctorCat V I) := ColimitMonoidal.monoidalCategory d
  let : MonObj (⟨S⟩ : EnrichedFunctorCat V I) := LaxMonoid.monObj d S L
  intro M f
  rfl

/-- Source Hom evaluation uses that actual carrier-typed unit insertion. -/
theorem sourceHom_apply_generator (n : I) (X : V) :
    letI := ColimitMonoidal.monoidalCategory d
    letI := LaxMonoid.monObj d S L
    ∀ (M : CommutativeModuleConversion.RightModule (⟨S⟩ : EnrichedFunctorCat V I))
      (q : (sourceFree d S L n).obj X ⟶ M),
      sourceHom d S L n X M q =
        Free.evaluate n X M.X (sourceGenerator d S L n X ≫ q.hom) := by
  intro M q
  exact @Primitive.hom_apply_generator V _ _ _ _ I _
    (ColimitMonoidal.monoidalCategory d) (⟨S⟩ : EnrichedFunctorCat V I)
    (LaxMonoid.monObj d S L) n X M q

/-- Source Hom extension has the actual whole carrier-typed original extension. -/
theorem sourceHom_symm_hom_carrier (n : I) (X : V) :
    letI := ColimitMonoidal.monoidalCategory d
    letI := LaxMonoid.monObj d S L
    ∀ (M : CommutativeModuleConversion.RightModule (⟨S⟩ : EnrichedFunctorCat V I))
      (f : X ⟶ M.X.toEnrichedFunctor.obj n),
      ((sourceHom d S L n X M).symm f).hom = sourceExtension d S L n X M f := by
  intro M f
  exact @Primitive.hom_symm_hom V _ _ _ _ I _
    (ColimitMonoidal.monoidalCategory d) (⟨S⟩ : EnrichedFunctorCat V I)
    (LaxMonoid.monObj d S L) n X M f

/-- The complete inverse function is the actual I-space extension followed by the stock action. -/
theorem sourceHom_symm_hom (n : I) (X : V) :
    letI := ColimitMonoidal.monoidalCategory d
    letI := LaxMonoid.monObj d S L
    ∀ (M : CommutativeModuleConversion.RightModule (⟨S⟩ : EnrichedFunctorCat V I))
      (f : X ⟶ M.X.toEnrichedFunctor.obj n),
      ((sourceHom d S L n X M).symm f).hom =
        (Free.extend n X M.X f ▷ (⟨S⟩ : EnrichedFunctorCat V I)) ≫ M.action := by
  intro M f
  simpa only [sourceExtension, Primitive.extension] using
    (sourceHom_symm_hom_carrier d S L n X M f)


/-- Both actual source functions recover every entire original module morphism. -/
theorem sourceHom_left_inv (n : I) (X : V) :
    letI := ColimitMonoidal.monoidalCategory d
    letI := LaxMonoid.monObj d S L
    ∀ (M : CommutativeModuleConversion.RightModule (⟨S⟩ : EnrichedFunctorCat V I))
      (q : (sourceFree d S L n).obj X ⟶ M),
      (sourceHom d S L n X M).symm (sourceHom d S L n X M q) = q := by
  intro M q
  exact (sourceHom d S L n X M).symm_apply_apply q

/-- Both actual source functions recover every original coefficient arrow. -/
theorem sourceHom_right_inv (n : I) (X : V) :
    letI := ColimitMonoidal.monoidalCategory d
    letI := LaxMonoid.monObj d S L
    ∀ (M : CommutativeModuleConversion.RightModule (⟨S⟩ : EnrichedFunctorCat V I))
      (f : X ⟶ M.X.toEnrichedFunctor.obj n),
      sourceHom d S L n X M ((sourceHom d S L n X M).symm f) = f := by
  intro M f
  exact @Primitive.hom_right_inv V _ _ _ _ I _
    (ColimitMonoidal.monoidalCategory d) (⟨S⟩ : EnrichedFunctorCat V I)
    (LaxMonoid.monObj d S L) n X M f

/-- Every original coefficient arrow is retained by the complete source extension. -/
theorem sourceHom_extend_precompose (n : I) {X Y : V} (f : X ⟶ Y) :
    letI := ColimitMonoidal.monoidalCategory d
    letI := LaxMonoid.monObj d S L
    ∀ (M : CommutativeModuleConversion.RightModule (⟨S⟩ : EnrichedFunctorCat V I))
      (g : Y ⟶ M.X.toEnrichedFunctor.obj n),
      (sourceHom d S L n X M).symm (f ≫ g) =
        (sourceFree d S L n).map f ≫ (sourceHom d S L n Y M).symm g := by
  intro M g
  exact @Primitive.hom_extend_precompose V _ _ _ _ I _
    (ColimitMonoidal.monoidalCategory d) (⟨S⟩ : EnrichedFunctorCat V I)
    (LaxMonoid.monObj d S L) n X Y f M g

/-- The genuine original source unit is identity-evaluation of its actual free carrier. -/
theorem sourceUnit_evaluation (n : I) (X : V) :
    letI := ColimitMonoidal.monoidalCategory d
    letI := LaxMonoid.monObj d S L
    (sourceAdjunction d S L n).unit.app X =
      sourceHom d S L n X ((sourceFree d S L n).obj X) (𝟙 _) := by
  exact @Primitive.unit_evaluation V _ _ _ _ I _
    (ColimitMonoidal.monoidalCategory d) (⟨S⟩ : EnrichedFunctorCat V I)
    (LaxMonoid.monObj d S L) n X

/-- The original source counit is the whole extension of the original level identity. -/
theorem sourceCounit_extension (n : I) :
    letI := ColimitMonoidal.monoidalCategory d
    letI := LaxMonoid.monObj d S L
    ∀ M : CommutativeModuleConversion.RightModule (⟨S⟩ : EnrichedFunctorCat V I),
      Primitive.CounitExtensionFormula (⟨S⟩ : EnrichedFunctorCat V I) n M := by
  intro M
  exact @Primitive.counit_extension V _ _ _ _ I _
    (ColimitMonoidal.monoidalCategory d) (⟨S⟩ : EnrichedFunctorCat V I)
    (LaxMonoid.monObj d S L) n M

/-- The actual original free unit and counit satisfy the complete source free triangle. -/
theorem sourceFree_triangle (n : I) (X : V) :
    letI : MonoidalCategory (EnrichedFunctorCat V I) := ColimitMonoidal.monoidalCategory d
    letI : MonObj (⟨S⟩ : EnrichedFunctorCat V I) := LaxMonoid.monObj d S L
    Primitive.FreeTriangleFormula (⟨S⟩ : EnrichedFunctorCat V I) n X := by
  exact @Primitive.free_triangle V _ _ _ _ I _
    (ColimitMonoidal.monoidalCategory d) (⟨S⟩ : EnrichedFunctorCat V I)
    (LaxMonoid.monObj d S L) n X

/-- The actual original evaluation unit and counit satisfy the full source evaluation triangle. -/
theorem sourceEvaluation_triangle (n : I) :
    letI := ColimitMonoidal.monoidalCategory d
    letI := LaxMonoid.monObj d S L
    ∀ M : CommutativeModuleConversion.RightModule (⟨S⟩ : EnrichedFunctorCat V I),
      (sourceAdjunction d S L n).unit.app ((sourceEvaluation d S L n).obj M) ≫
        (sourceEvaluation d S L n).map ((sourceAdjunction d S L n).counit.app M) =
      𝟙 ((sourceEvaluation d S L n).obj M) := by
  intro M
  exact @Primitive.evaluation_triangle V _ _ _ _ I _
    (ColimitMonoidal.monoidalCategory d) (⟨S⟩ : EnrichedFunctorCat V I)
    (LaxMonoid.monObj d S L) n M

end CategoryTheory.Enriched.RightModuleFreeEvaluation
