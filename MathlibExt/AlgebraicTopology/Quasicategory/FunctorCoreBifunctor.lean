/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.Quasicategory.CoreWeakEquivalence
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal.MappingSpaceW
import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Inner.PushoutProduct

/-!
# The actual cores of simplicial functor objects

The source parameter is contravariant. Objects of these cores are all
simplicial functors, including functors with noninvertible input edges.
The core restricts transformations rather than the input functors.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed Opposite
open scoped Simplicial

namespace SSet.FunctorCore

/-- The literal equivalence-edge core of the full simplicial functor object. -/
abbrev functor (K : SSet.{u}) : SSet.{u} ⥤ SSet.{u} := ihom K ⋙ coreFunctor

/-- The same functor objects form a contravariant/covariant bifunctor. -/
def bifunctor : SSet.{u}ᵒᵖ ⥤ SSet.{u} ⥤ SSet.{u} :=
  MonoidalClosed.internalHom ⋙ (Functor.whiskeringRight SSet.{u} SSet.{u} SSet.{u}).obj coreFunctor

/-- Its source action is the original internal precomposition followed by core. -/
def sourceMap {K L : SSet.{u}} (a : K ⟶ L) : functor L ⟶ functor K :=
  Functor.whiskerRight (MonoidalClosed.pre a) coreFunctor

/-- The full bifunctor retains its literal original source map. -/
theorem bifunctor_map {K L : SSet.{u}} (a : K ⟶ L) : bifunctor.map a.op = sourceMap a := rfl

/-- Every source component is the core of the entire original precomposition map. -/
theorem sourceMap_app {K L : SSet.{u}} (a : K ⟶ L) (X : SSet.{u}) :
    (sourceMap a).app X = core.map ((MonoidalClosed.pre a).app X) := rfl

/-- Source identity is retained as an equality of whole natural transformations. -/
theorem sourceMap_id (K : SSet.{u}) : sourceMap (𝟙 K) = 𝟙 (functor K) := by
  change bifunctor.map (𝟙 (op K)) = 𝟙 (bifunctor.obj (op K))
  exact bifunctor.map_id (op K)

/-- Source composition retains the original contravariant order. -/
theorem sourceMap_comp {K L M : SSet.{u}} (a : K ⟶ L) (b : L ⟶ M) :
    sourceMap (a ≫ b) = sourceMap b ≫ sourceMap a := by
  change bifunctor.map (b.op ≫ a.op) = bifunctor.map b.op ≫ bifunctor.map a.op
  exact bifunctor.map_comp b.op a.op

/-- Source precomposition is natural in the whole original target map. -/
theorem sourceMap_natural {K L X Y : SSet.{u}} (a : K ⟶ L) (f : X ⟶ Y) :
    (functor L).map f ≫ (sourceMap a).app Y = (sourceMap a).app X ≫ (functor K).map f :=
  (sourceMap a).naturality f

/-- Both full functor cores are genuinely Kan at every quasicategory target. -/
theorem isKan (K X : SSet.{u}) [Quasicategory X] : KanComplex ((functor K).obj X) := by
  change KanComplex (core ((ihom K).obj X) : SSet.{u})
  infer_instance

/-- Target categorical equivalences induce structural Kan weak maps on the same full functor cores. -/
theorem map_weak {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    (f : X ⟶ Y) (hf : categoricalEquivalences f) (K : SSet.{u}) :
    KanComplex.W ((functor K).map f) :=
  core_map_mem_W_of_categoricalEquivalence (hf.ihomMap K)

/-- The target core inclusion retains the entire internal postcomposition square. -/
theorem map_inclusion {K X Y : SSet.{u}} (f : X ⟶ Y) :
    (functor K).map f ≫ (core ((ihom K).obj Y)).ι =
      (core ((ihom K).obj X)).ι ≫ (ihom K).map f := core.map_ι _

/-- The source core inclusion retains the entire internal precomposition square. -/
theorem sourceMap_inclusion {K L : SSet.{u}} (a : K ⟶ L) (X : SSet.{u}) :
    (sourceMap a).app X ≫ (core ((ihom K).obj X)).ι =
      (core ((ihom L).obj X)).ι ≫ (MonoidalClosed.pre a).app X := core.map_ι _

/-- Evaluation uses the original full functor object and its original core inclusion. -/
def evaluation (K X : SSet.{u}) : K ⊗ (functor K).obj X ⟶ X :=
  K ◁ (core ((ihom K).obj X)).ι ≫ (ihom.ev K).app X

/-- Whole evaluation is natural in the original target, including every source parameter simplex. -/
theorem evaluation_natural {K X Y : SSet.{u}} (f : X ⟶ Y) :
    K ◁ (functor K).map f ≫ evaluation K Y = evaluation K X ≫ f := by
  dsimp only [evaluation]
  rw [← Category.assoc, ← MonoidalCategory.whiskerLeft_comp, map_inclusion,
    MonoidalCategory.whiskerLeft_comp, Category.assoc, ihom.ev_naturality]
  exact (Category.assoc _ _ _).symm

/-- Whole evaluation keeps the same source precomposition and the complete source change. -/
theorem evaluation_source {K L : SSet.{u}} (a : K ⟶ L) (X : SSet.{u}) :
    K ◁ (sourceMap a).app X ≫ evaluation K X =
      a ▷ (functor L).obj X ≫ evaluation L X := by
  dsimp only [evaluation]
  rw [← Category.assoc, ← MonoidalCategory.whiskerLeft_comp, sourceMap_inclusion,
    MonoidalCategory.whiskerLeft_comp, Category.assoc, id_tensor_pre_app_comp_ev]
  rw [whisker_exchange_assoc]

/-- Every original simplicial functor is an individual vertex of the full functor core. -/
def vertex {K X : SSet.{u}} (f : K ⟶ X) : ((functor K).obj X) _⦋0⦌ :=
  ⟨ihomVertexEquiv K X f, mem_core_obj_zero _⟩

/-- Target transport retains the individual original functor, not just its component class. -/
theorem map_vertex {K X Y : SSet.{u}} (f : K ⟶ X) (g : X ⟶ Y) :
    ((functor K).map g).app (op ⦋0⦌) (vertex f) = vertex (f ≫ g) := by
  apply Subtype.ext
  change ((ihom K).map g).app (op ⦋0⦌) (ihomVertexEquiv K X f) = ihomVertexEquiv K Y (f ≫ g)
  exact congrArg (fun h : 𝟙_ SSet.{u} ⟶ (ihom K).obj Y => h.app (op ⦋0⦌) PUnit.unit)
    (MonoidalClosed.curry'_ihom_map f g)

end SSet.FunctorCore
