/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Orthogonal.CanonicalSourceRightModuleEquivalence
import MathlibExt.CategoryTheory.Enriched.FreeAdjunctionSource
import MathlibExt.CategoryTheory.Enriched.FreeHomTransport
import MathlibExt.CategoryTheory.Enriched.RightModuleFreeEvaluation

/-!
# Original orthogonal free right modules and evaluation

The source free functor is the actual free continuous I-space followed by
the stock right sphere-module free functor. Its carrier is therefore the
original Day convolution of that free I-space with the representation sphere.
Its adjunction evaluates the unchanged original module I-space. The proved
carrier equivalence identifies this adjunction with native enriched
free/evaluation, retaining both original Hom functions, the actual free
unit and action counit, every coefficient map and the original inverse
carrier comparison.

The source is MMSS Construction 2.1, Theorem 2.2 and Example 4.4, together
with Section 23, in *Model categories of diagram spectra*, December 30,
1999 preprint, pages 9, 12–13 and 63. Both categories use the original
right-module convention. No left-module conversion or chosen free-object
dictionary is assumed here.
-/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u v

open CategoryTheory MonoidalCategory MonoidalOpposite
open CategoryTheory.Spectra CategoryTheory.Enriched.SphereOperator
open CategoryTheory.Spectra.OrthogonalSourceRightModule
open scoped MonoidalClosed

namespace PointedCGWH.Spectra.Orthogonal.CanonicalSourceRightModuleFreeEvaluation

attribute [local instance] OrthogonalIndex.category OrthogonalIndex.monoidalCategory
attribute [local instance] OrthogonalIndex.enrichedOrdinaryCategory
attribute [local instance] OrthogonalIndex.symmetricCategory
attribute [local instance]
  NativeSphereModule.instMonoidalCategoryEnrichedFunctorCatOrthogonalIndex
  NativeSphereModule.instMonObjEnrichedFunctorCatOrthogonalIndexSphereISpace

attribute [local instance] Enriched.prodCategory
attribute [local instance] MonoidalLeftAction.monoidalOppositeLeftAction

open EnrichedFunctorCat CanonicalSourceRightModuleActions CanonicalSourceRightModuleEquivalence
open CategoryTheory.Enriched.RightModuleFreeEvaluation

/-- The actual original free I-space followed by the stock right sphere-module free functor. -/
def freeFunctor (n : OrthogonalIndex) : PointedCGWH.{u, v} ⥤ SourceModule.{u, v} :=
  CategoryTheory.Enriched.RightModuleFreeEvaluation.Primitive.free sphereISpace.{u, v} n

/-- The original complete right-free module on an arbitrary coefficient space. -/
abbrev freeObject (n : OrthogonalIndex) (X : PointedCGWH.{u, v}) : SourceModule.{u, v} :=
  (freeFunctor n).obj X

/-- Source evaluation forgets the stock module action and evaluates its unchanged I-space. -/
def evaluation (n : OrthogonalIndex) : SourceModule.{u, v} ⥤ PointedCGWH.{u, v} :=
  CategoryTheory.Enriched.RightModuleFreeEvaluation.Primitive.evaluation sphereISpace.{u, v} n

/-- Every evaluated source object is the complete original level space. -/
theorem evaluation_obj (n : OrthogonalIndex) (M : SourceModule.{u, v}) :
    (evaluation n).obj M = M.X.toEnrichedFunctor.obj n := rfl

/-- Every evaluated source arrow is the entire original enriched component. -/
theorem evaluation_map (n : OrthogonalIndex) {M N : SourceModule.{u, v}} (q : M ⟶ N) :
    (evaluation n).map q = component q.hom n := rfl

/-- The source free carrier is the actual right Day tensor of the actual free I-space. -/
theorem freeObject_X (n : OrthogonalIndex) (X : PointedCGWH.{u, v}) :
    (freeObject n X).X = Free.object n X ⊗ sphereISpace.{u, v} := rfl

/-- The entire free right action is the actual Day associator followed by sphere multiplication. -/
abbrev freeObjectAction := fun n X =>
  RightModuleFree.freeObject_action sphereISpace.{u, v} (Free.object n X)

/-- The source adjunction is composed from the original two actual free/evaluation adjunctions. -/
def adjunction (n : OrthogonalIndex) : freeFunctor.{u, v} n ⊣ evaluation n :=
  CategoryTheory.Enriched.RightModuleFreeEvaluation.Primitive.adjunction sphereISpace.{u, v} n

/-- The complete original source Hom correspondence, in the original right-free order. -/
abbrev homEquiv := fun n => (adjunction.{u, v} n).homEquiv

/-- Original source evaluation first evaluates the free-module generator, then the index
identity. -/
abbrev evaluate := fun n X M => (homEquiv.{u, v} n X M).toFun

/-- Original source extension uses the free I-space extension and the actual right-module action. -/
abbrev extend := fun n X M => (homEquiv.{u, v} n X M).invFun

/-- The chosen source adjunction has the same complete original Hom functions. -/
theorem adjunction_homEquiv (n : OrthogonalIndex) (X : PointedCGWH.{u, v})
    (M : SourceModule.{u, v}) : (adjunction n).homEquiv X M = homEquiv n X M := rfl

/-- The original stock unit insertion, typed on the unchanged actual free carrier. -/
abbrev generator := CategoryTheory.Enriched.RightModuleFreeEvaluation.Primitive.generator sphereISpace.{u, v}

/-- The generator retains the whole original stock unit map and its own complete source type. -/
theorem generator_original (n : OrthogonalIndex) (X : PointedCGWH.{u, v}) :
    HEq (Primitive.generator sphereISpace.{u, v} n X)
      (RightModuleFree.freeGenerator sphereISpace.{u, v} (Free.object n X)) :=
  Primitive.generator_original sphereISpace.{u, v} n X

/-- The complete original evaluation uses the stock unit insertion and original I-space identity. -/
theorem evaluate_formula (n : OrthogonalIndex) (X : PointedCGWH.{u, v})
    (M : CommutativeModuleConversion.RightModule sphereISpace.{u, v})
    (q : (Primitive.free sphereISpace.{u, v} n).obj X ⟶ M) :
    (Primitive.adjunction sphereISpace.{u, v} n).homEquiv X M q =
      Free.evaluate n X M.X (Primitive.generator sphereISpace.{u, v} n X ≫ q.hom) :=
  Primitive.hom_apply_generator sphereISpace.{u, v} n X M q

/-- The whole forward Hom function is the original generator/identity evaluation. -/
theorem homEquiv_apply (n : OrthogonalIndex) (X : PointedCGWH.{u, v}) (M : SourceModule.{u, v})
    (q : freeObject n X ⟶ M) : homEquiv n X M q = evaluate n X M q := rfl

/-- The whole inverse Hom function is the actual original two-stage extension. -/
theorem homEquiv_symm_apply (n : OrthogonalIndex) (X : PointedCGWH.{u, v})
    (M : SourceModule.{u, v}) (f : X ⟶ M.X.toEnrichedFunctor.obj n) :
    (homEquiv n X M).symm f = extend n X M f := rfl

/-- Both actual source functions recover every entire original module morphism. -/
abbrev extendEvaluate := fun n X M => (homEquiv.{u, v} n X M).symm_apply_apply

/-- Both actual source functions recover every original coefficient map. -/
theorem evaluate_extend (n : OrthogonalIndex) (X : PointedCGWH.{u, v})
    (M : SourceModule.{u, v}) (f : X ⟶ (evaluation n).obj M) :
    homEquiv n X M ((homEquiv n X M).symm f) = f :=
  (homEquiv n X M).apply_symm_apply f

/-- The original free-I extension and stock right action on the actual free carrier. -/
abbrev extensionCarrier := fun n X M f => (extend.{u, v} n X M f).hom

/-- The complete extension retains the original tensored free map and target action. -/
theorem extensionCarrier_original (n : OrthogonalIndex) (X : PointedCGWH.{u, v})
    (M : CommutativeModuleConversion.RightModule sphereISpace.{u, v})
    (f : X ⟶ M.X.toEnrichedFunctor.obj n) :
    (((Primitive.adjunction sphereISpace.{u, v} n).homEquiv X M).symm f).hom =
      (Free.extend n X M.X f ▷ sphereISpace.{u, v}) ≫ M.action :=
  Primitive.hom_symm_hom sphereISpace.{u, v} n X M f

/-- Every coefficient map is the actual free-I map followed by the original stock right-free map. -/
theorem freeFunctor_map_hom (n : OrthogonalIndex) {X Y : PointedCGWH.{u, v}} (f : X ⟶ Y) :
    ((freeFunctor n).map f).hom = Free.coefficientMap n f ▷ sphereISpace.{u, v} := rfl

/-- The complete native/source evaluation comparison uses identities on the original level
spaces. -/
def evaluationComparison (n : OrthogonalIndex) :
    fromModuleFunctor.{u, v} ⋙
      EnrichedFunctorCat.evaluation (OrthogonalOperatorIndex.ofIndex.{u, v} n) ≅
      evaluation n :=
  NatIso.ofComponents (fun M => Iso.refl (M.X.toEnrichedFunctor.obj n)) (by
    intro M N q
    change component (fromModuleFunctor.map q) (OrthogonalOperatorIndex.ofIndex.{u, v} n) ≫
      𝟙 (N.X.toEnrichedFunctor.obj n) = 𝟙 (M.X.toEnrichedFunctor.obj n) ≫ component q.hom n
    exact (Category.comp_id _).trans
      ((fromModuleFunctor_map_component q n).trans (Category.id_comp _).symm))

/-- Every forward evaluation comparison is the original identity on the original level space. -/
theorem evaluationComparison_hom_app (n : OrthogonalIndex) (M : SourceModule.{u, v}) :
    (evaluationComparison n).hom.app M = 𝟙 (M.X.toEnrichedFunctor.obj n) := rfl

/-- Every inverse evaluation comparison is the original identity on that same level space. -/
theorem evaluationComparison_inv_app (n : OrthogonalIndex) (M : SourceModule.{u, v}) :
    (evaluationComparison n).inv.app M = 𝟙 (M.X.toEnrichedFunctor.obj n) := rfl

/-- The actual free right sphere modules are naturally isomorphic to the source images of native
frees. -/
def freeComparison (n : OrthogonalIndex) :
    freeFunctor.{u, v} n ≅
      Free.functor (OrthogonalOperatorIndex.ofIndex.{u, v} n) ⋙ toModuleFunctor :=
  FreeAdjunctionSource.comparison equivalence.symm (OrthogonalOperatorIndex.ofIndex.{u, v} n)
    (freeFunctor n) (evaluation n) (adjunction n) (evaluationComparison n)

/-- The complete original free source comparison on an arbitrary coefficient space. -/
def freeModuleIso (n : OrthogonalIndex) (X : PointedCGWH.{u, v}) :
    freeObject n X ≅ toModule (Free.object (OrthogonalOperatorIndex.ofIndex.{u, v} n) X) :=
  (freeComparison n).app X

/-- The complete source free functor reconstructs the actual native enriched free functor. -/
def operatorFreeComparison (n : OrthogonalIndex) :
    freeFunctor.{u, v} n ⋙ fromModuleFunctor ≅
      Free.functor (OrthogonalOperatorIndex.ofIndex.{u, v} n) :=
  FreeAdjunctionSource.operatorIso equivalence.symm (OrthogonalOperatorIndex.ofIndex.{u, v} n)
    (freeFunctor n) (evaluation n) (adjunction n) (evaluationComparison n)

/-- The genuine native free isomorphism retains the original stock right-free module. -/
def nativeFreeIso (n : OrthogonalIndex) (X : PointedCGWH.{u, v}) :
    fromModule (freeObject n X) ≅ Free.object (OrthogonalOperatorIndex.ofIndex.{u, v} n) X :=
  (operatorFreeComparison n).app X

/-- The inverse native free map uses the original carrier unit and the original stock free
comparison. -/
theorem nativeFreeIso_inv (n : OrthogonalIndex) (X : PointedCGWH.{u, v}) :
    (nativeFreeIso n X).inv = equivalence.unitIso.hom.app
        (Free.object (OrthogonalOperatorIndex.ofIndex.{u, v} n) X) ≫
      fromModuleFunctor.map (freeModuleIso n X).inv :=
  FreeAdjunctionSource.operatorIso_inv_app equivalence.symm
    (OrthogonalOperatorIndex.ofIndex.{u, v} n) (freeFunctor n) (evaluation n)
    (adjunction n) (evaluationComparison n) X

/-- Original source free evaluation and native free evaluation retain the exact same coefficient
arrow. -/
theorem evaluation_square (n : OrthogonalIndex) (X : PointedCGWH.{u, v}) (M : SourceModule.{u, v})
    (q : freeObject n X ⟶ M) :
    evaluate n X M q = Free.evaluate (OrthogonalOperatorIndex.ofIndex.{u, v} n) X (fromModule M)
      ((nativeFreeIso n X).inv ≫ fromModuleFunctor.map q) := by
  have h := FreeAdjunctionSource.point equivalence.symm (OrthogonalOperatorIndex.ofIndex.{u, v} n)
    (freeFunctor n) (evaluation n) (adjunction n) (evaluationComparison n) q
  change evaluate n X M q ≫ (evaluationComparison n).inv.app M = _ at h
  exact ((congrArg (fun r => evaluate n X M q ≫ r)
    (evaluationComparison_inv_app n M)).trans (Category.comp_id _)).symm.trans h

/-- Native extension and the original two-stage source extension commute as whole morphisms. -/
theorem extension_square (n : OrthogonalIndex) (X : PointedCGWH.{u, v}) (M : SourceModule.{u, v})
    (f : X ⟶ M.X.toEnrichedFunctor.obj n) :
    (nativeFreeIso n X).inv ≫ fromModuleFunctor.map (extend n X M f) =
      Free.extend (OrthogonalOperatorIndex.ofIndex.{u, v} n) X (fromModule M) f := by
  apply (Free.homEquiv (OrthogonalOperatorIndex.ofIndex.{u, v} n) X (fromModule M)).injective
  exact ((evaluation_square n X M (extend n X M f)).symm.trans
    (evaluate_extend n X M f)).trans
      (Free.evaluate_extend (OrthogonalOperatorIndex.ofIndex.{u, v} n) X (fromModule M) f).symm

/-- The original coefficient maps commute with the complete source free comparison. -/
theorem freeModuleIso_coefficient (n : OrthogonalIndex) {X Y : PointedCGWH.{u, v}} (f : X ⟶ Y) :
    (freeFunctor n).map f ≫ (freeModuleIso n Y).hom =
      (freeModuleIso n X).hom ≫ toModuleFunctor.map
        (Free.coefficientMap (OrthogonalOperatorIndex.ofIndex.{u, v} n) f) :=
  (freeComparison n).hom.naturality f

/-- Inverse source free comparisons retain those same original coefficient arrows. -/
theorem freeModuleIso_inv_coefficient (n : OrthogonalIndex) {X Y : PointedCGWH.{u, v}} (f : X ⟶ Y) :
    toModuleFunctor.map (Free.coefficientMap (OrthogonalOperatorIndex.ofIndex.{u, v} n) f) ≫
      (freeModuleIso n Y).inv = (freeModuleIso n X).inv ≫ (freeFunctor n).map f :=
  (freeComparison n).inv.naturality f

/-- The native free comparison retains the entire original coefficient naturality square. -/
theorem nativeFreeIso_coefficient (n : OrthogonalIndex) {X Y : PointedCGWH.{u, v}} (f : X ⟶ Y) :
    fromModuleFunctor.map ((freeFunctor n).map f) ≫ (nativeFreeIso n Y).hom =
      (nativeFreeIso n X).hom ≫ Free.coefficientMap (OrthogonalOperatorIndex.ofIndex.{u, v} n) f :=
  (operatorFreeComparison n).hom.naturality f

/-- Source free evaluation is natural under every entire original target module morphism. -/
theorem evaluate_postcomp (n : OrthogonalIndex) (X : PointedCGWH.{u, v})
    {M N : SourceModule.{u, v}} (q : freeObject n X ⟶ M) (r : M ⟶ N) :
    evaluate n X N (q ≫ r) = evaluate n X M q ≫ component r.hom n := by
  have h := (adjunction n).homEquiv_naturality_right q r
  exact h

/-- Source free extension is natural under every actual coefficient map. -/
theorem extend_precompose (n : OrthogonalIndex) {X Y : PointedCGWH.{u, v}} (f : X ⟶ Y)
    (M : CommutativeModuleConversion.RightModule sphereISpace.{u, v})
    (g : Y ⟶ M.X.toEnrichedFunctor.obj n) :
    ((Primitive.adjunction sphereISpace.{u, v} n).homEquiv X M).symm (f ≫ g) =
      (Primitive.free sphereISpace.{u, v} n).map f ≫
        ((Primitive.adjunction sphereISpace.{u, v} n).homEquiv Y M).symm g :=
  Primitive.hom_extend_precompose sphereISpace.{u, v} n f M g

/-- The source adjunction's original unit remains the identity-evaluated free module generator. -/
theorem unit_evaluation (n : OrthogonalIndex) (X : PointedCGWH.{u, v}) :
    (adjunction n).unit.app X = (adjunction n).homEquiv X ((freeFunctor n).obj X) (𝟙 _) :=
  ((adjunction n).homEquiv_id X).symm

/-- The source adjunction's actual counit is the original action extension of the level identity. -/
theorem counit_extension (n : OrthogonalIndex) (M : SourceModule.{u, v}) :
    (adjunction n).counit.app M =
      ((adjunction n).homEquiv ((evaluation n).obj M) M).symm (𝟙 ((evaluation n).obj M)) :=
  ((adjunction n).homEquiv_symm_id M).symm

/-- The exact original source free unit and source action counit satisfy the full free triangle. -/
abbrev freeTriangle := fun n => (adjunction.{u, v} n).left_triangle_components

/-- The original evaluation unit and action counit satisfy the full evaluation triangle. -/
theorem evaluation_triangle (n : OrthogonalIndex) (M : SourceModule.{u, v}) :
    (adjunction n).unit.app ((evaluation n).obj M) ≫
      (evaluation n).map ((adjunction n).counit.app M) = 𝟙 ((evaluation n).obj M) :=
  (adjunction n).right_triangle_components M

end PointedCGWH.Spectra.Orthogonal.CanonicalSourceRightModuleFreeEvaluation
