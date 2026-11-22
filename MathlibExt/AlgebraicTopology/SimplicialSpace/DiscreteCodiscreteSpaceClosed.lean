/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.BoxProduct
import MathlibExt.AlgebraicTopology.SimplicialSpace.SegalExponentClosure
import MathlibExt.AlgebraicTopology.SimplicialSet.CodiscreteVertexClosed
import MathlibExt.AlgebraicTopology.SimplicialSet.ConnectedComponents.Products
import MathlibExt.AlgebraicTopology.SimplicialSet.PiZeroConstantAdjunction
import Mathlib.CategoryTheory.Adjunction.Whiskering
import Mathlib.CategoryTheory.Monoidal.Closed.Functor

/-!
# The actual π0-at-outer-zero adjunction and classifying whole powers

Both ordinary adjoints are constructed from the native original nerve and
inner-constant maps. No model category, localization, completion outcome,
closed-power Iso or mapping-fibre weak condition is supplied as an input.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory MonoidalClosed
open scoped Simplicial SimplicialSpace.Cartesian
namespace SimplicialSpace.DiscreteCodiscreteSpaceClosed

/-- The actual original discrete-inner embedding has a concrete inverse on its Hom sets. -/
def discretePreimage {X Y : SSet.{u}}
    (f : discreteInnerFunctor.obj X ⟶ discreteInnerFunctor.obj Y) : X ⟶ Y where
  app n := (f.hom.app n).app (op ⦋0⦌)
  naturality _n _m θ := congrArg (fun k => k.app (op ⦋0⦌)) (f.hom.naturality θ)

/-- Every inner degree of a map between original inner-constant objects is its zero degree. -/
theorem discrete_map_preimage {X Y : SSet.{u}}
    (f : discreteInnerFunctor.obj X ⟶ discreteInnerFunctor.obj Y) :
    discreteInnerFunctor.map (discretePreimage f) = f := by
  apply SimplicialSpace.homEquiv.injective
  apply NatTrans.ext
  funext m
  apply NatTrans.ext
  funext n
  change (f.hom.app m).app (op ⦋0⦌) = (f.hom.app m).app n
  have h := (f.hom.app m).naturality (n.unop.const ⦋0⦌ 0).op
  change (f.hom.app m).app n = (f.hom.app m).app (op ⦋0⦌) at h
  exact h.symm

/-- The embedding as simplicial spaces constant in the inner direction is fully faithful. -/
def discreteFullyFaithful : discreteInnerFunctor.{u}.FullyFaithful where
  preimage := discretePreimage
  map_preimage := discrete_map_preimage
  preimage_map _f := rfl

/-- The target is exactly D of the original codiscrete nerve, retaining the designated carrier. -/
def codiscreteSpaceFunctor : Type u ⥤ SimplicialSpace.{u} :=
  CategoryTheory.Codiscrete.functorToSSet ⋙ discreteInnerFunctor

/-- The left functor retains all inner component quotients before taking original outer zero. -/
def componentRows : SimplicialSpace.{u} ⥤ SSet.{u} :=
  forget ⋙ (Functor.whiskeringRight SimplexCategoryᵒᵖ SSet.{u} (Type u)).obj SSet.π₀Functor

/-- The functor taking connected components in outer degree zero. -/
def componentZero : SimplicialSpace.{u} ⥤ Type u :=
  componentRows ⋙ (evaluation SimplexCategoryᵒᵖ (Type u)).obj (op ⦋0⦌)

theorem componentZero_obj (W : SimplicialSpace.{u}) :
    componentZero.obj W = SSet.π₀ (W.diagram.obj (op ⦋0⦌)) := rfl

/-- The actual original inner-component/discrete-inner adjunction, through the carrier
equivalence. -/
def componentRowsAdjunction : componentRows.{u} ⊣ discreteInnerFunctor.{u} :=
  equivalenceSimplicialObject.toAdjunction.comp
    (SSet.PiZeroConstantAdjunction.adjunction.whiskerRight SimplexCategoryᵒᵖ)

/-- The classifying adjunction is genuinely π0(W0) ⊣ D of the codiscrete nerve. -/
def componentZeroAdjunction : componentZero.{u} ⊣ codiscreteSpaceFunctor.{u} :=
  componentRowsAdjunction.comp SSet.CodiscreteVertexClosed.vertexAdjunction

/-- The codiscrete nerve embedding into simplicial spaces is fully faithful. -/
def codiscreteSpaceFullyFaithful : codiscreteSpaceFunctor.{u}.FullyFaithful :=
  SSet.CodiscreteVertexClosed.codiscreteFullyFaithful.comp discreteFullyFaithful

/-- Every binary product is preserved by the genuine inner π0 and outer evaluation left functor. -/
theorem componentZero_preservesBinaryProducts :
    PreservesLimitsOfShape (Discrete WalkingPair) componentZero.{u} := by
  dsimp only [componentZero, componentRows]
  infer_instance

/-- Product preservation is constructed on the actual original codiscrete/discrete-inner functor. -/
theorem codiscreteSpace_preservesBinaryProducts :
    PreservesLimitsOfShape (Discrete WalkingPair) codiscreteSpaceFunctor.{u} := by
  dsimp only [codiscreteSpaceFunctor, discreteInnerFunctor, SSet.simplicialSpaceDiscrete]
  infer_instance

attribute [local instance] codiscreteSpace_preservesBinaryProducts

/-- Whole Cartesian power comparison follows from the actual fully faithful right adjoint. -/
theorem codiscreteSpaceClosed : MonoidalClosedFunctor codiscreteSpaceFunctor.{u} := by
  let _ := codiscreteSpaceFullyFaithful.full
  let _ := codiscreteSpaceFullyFaithful.faithful
  let _ := componentZero_preservesBinaryProducts
  exact cartesianClosedFunctorOfLeftAdjointPreservesBinaryProducts
    codiscreteSpaceFunctor.{u} componentZeroAdjunction

/-- The SAME whole power comparison is the native adjoint comparison, before any row evaluation. -/
def wholePowerIso (A B : Type u) :
    codiscreteSpaceFunctor.obj ((ihom A).obj B) ≅
      (ihom (codiscreteSpaceFunctor.obj A)).obj (codiscreteSpaceFunctor.obj B) := by
  let _ := codiscreteSpaceClosed
  exact asIso ((expComparison codiscreteSpaceFunctor A).app B)

theorem wholePowerIso_evaluation (A B : Type u) :
    codiscreteSpaceFunctor.obj A ◁ (wholePowerIso A B).hom ≫
      (ihom.ev (codiscreteSpaceFunctor.obj A)).app (codiscreteSpaceFunctor.obj B) =
    inv (CartesianMonoidalCategory.prodComparison codiscreteSpaceFunctor A ((ihom A).obj B)) ≫
      codiscreteSpaceFunctor.map ((ihom.ev A).app B) :=
  expComparison_ev codiscreteSpaceFunctor A B

/-- The native whole comparison preserves the actual currying adjunction. -/
theorem wholePowerIso_curry (A B Z : Type u) (f : A ⊗ B ⟶ Z) :
    codiscreteSpaceFunctor.map (curry f) ≫ (wholePowerIso A Z).hom =
      curry (inv (CartesianMonoidalCategory.prodComparison codiscreteSpaceFunctor A B) ≫
        codiscreteSpaceFunctor.map f) := by
  apply uncurry_injective
  have hu : uncurry (wholePowerIso A Z).hom =
      inv (CartesianMonoidalCategory.prodComparison codiscreteSpaceFunctor A ((ihom A).obj Z)) ≫
        codiscreteSpaceFunctor.map ((ihom.ev A).app Z) := by
    rw [uncurry_eq, wholePowerIso_evaluation]
  rw [uncurry_natural_left, hu, uncurry_curry,
    ← CartesianMonoidalCategory.prodComparison_inv_natural_whiskerLeft_assoc,
    ← Functor.map_comp, whiskerLeft_curry_ihom_ev_app]

/-- Full target naturality survives before diagonal or vertex evaluation. -/
theorem wholePowerIso_target {A B C : Type u} (f : B ⟶ C) :
    codiscreteSpaceFunctor.map ((ihom A).map f) ≫ (wholePowerIso A C).hom =
      (wholePowerIso A B).hom ≫
        (ihom (codiscreteSpaceFunctor.obj A)).map (codiscreteSpaceFunctor.map f) :=
  (expComparison codiscreteSpaceFunctor A).naturality f

/-- Full source naturality uses genuine contravariant precomposition. -/
theorem wholePowerIso_source {A A' : Type u} (f : A' ⟶ A) (B : Type u) :
    (wholePowerIso A B).hom ≫ (pre (codiscreteSpaceFunctor.map f)).app
        (codiscreteSpaceFunctor.obj B) =
    codiscreteSpaceFunctor.map ((pre f).app B) ≫ (wholePowerIso A' B).hom := by
  exact congrArg (fun η => η.app B) (expComparison_whiskerLeft codiscreteSpaceFunctor f)


/-- The outer-k counit is the actual quotient counit of the inner constant simplicial set. -/
theorem componentRowsAdjunction_counit_app (X : SSet.{u}) (k : SimplexCategoryᵒᵖ) :
    (componentRowsAdjunction.counit.app X).app k =
      (SSet.PiZeroConstantAdjunction.piZeroConstIso (X.obj k)).hom := by
  dsimp only [componentRowsAdjunction]
  rw [Adjunction.comp_counit_app]
  change (((Functor.whiskeringRight SimplexCategoryᵒᵖ SSet.{u} (Type u)).obj
      SSet.π₀Functor).map (𝟙 (SSet.simplicialSpaceDiscrete.obj X)) ≫
      (SSet.PiZeroConstantAdjunction.adjunction.whiskerRight SimplexCategoryᵒᵖ).counit.app
          X).app k = _
  rw [CategoryTheory.Functor.map_id, Category.id_comp,
    Adjunction.whiskerRight_counit_app_app]
  exact SSet.PiZeroConstantAdjunction.adjunction_counit (X.obj k)

/-- The classifying counit first takes the genuine inner component quotient, then the outer
vertex. -/
theorem componentZeroAdjunction_counit (A : Type u) :
    componentZeroAdjunction.counit.app A =
      (SSet.PiZeroConstantAdjunction.piZeroConstIso
        ((CategoryTheory.Codiscrete.functorToSSet.obj A).obj (op ⦋0⦌))).hom ≫
      (SSet.CodiscreteVertexClosed.vertexIso A).hom := by
  dsimp only [componentZeroAdjunction]
  rw [Adjunction.comp_counit_app]
  change (componentRowsAdjunction.counit.app
      (CategoryTheory.Codiscrete.functorToSSet.obj A)).app (op ⦋0⦌) ≫
      SSet.CodiscreteVertexClosed.vertexAdjunction.counit.app A = _
  rw [componentRowsAdjunction_counit_app,
    SSet.CodiscreteVertexClosed.vertexAdjunction_counit]
  rfl

/-- Evaluation of that SAME counit on a quotient representative is the full zero-nerve vertex. -/
theorem componentZeroAdjunction_counit_mk (A : Type u)
    (x : (CategoryTheory.Codiscrete.functorToSSet.obj A).obj (op ⦋0⦌)) :
    componentZeroAdjunction.counit.app A (SSet.π₀.mk x) =
      (SSet.CodiscreteVertexClosed.vertexIso A).hom x := by
  rw [componentZeroAdjunction_counit]
  rfl

end SimplicialSpace.DiscreteCodiscreteSpaceClosed
