/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.FixedObjectLabelPushforwardFunctor
import Mathlib.CategoryTheory.Adjunction.Basic

/-! # Arbitrary-label enriched pushforward is genuinely left adjoint to restriction

The two whole-map inverse laws and original source and target naturality
construct the actual adjunction. Its unit is the original source-generator
inclusion; its counit evaluates the presented original generators.
-/

noncomputable section
universe u
open CategoryTheory MonoidalCategory Opposite

namespace CategoryTheory.SimplicialEnrichment.FixedObjects.LabelPushforward

variable {A O : Type u} (a : A → O)

/-- The actual original path pushforward is left adjoint to the literal label restriction. -/
def adjunction : functor a ⊣ LabelRestriction.functor a :=
  Adjunction.mkOfHomEquiv {
    homEquiv := homEquiv a
    homEquiv_naturality_left_symm := by
      intro C E D F G
      change E ⟶ LabelRestriction.object a D at G
      change desc a C (F ≫ G) = map a F ≫ desc a E G
      apply (homEquiv a C D).injective
      rw [← homEquiv_symm_apply, Equiv.apply_symm_apply, homEquiv_source]
      rw [← homEquiv_symm_apply, Equiv.apply_symm_apply]
    homEquiv_naturality_right := homEquiv_target a }

/-- The actual adjunction unit is the same whole original source-generator map. -/
theorem unit_app (C : FixedObjects A) : (adjunction a).unit.app C = unit a C := by
  change unit a C ≫ (LabelRestriction.functor a).map (𝟙 (object a C)) = unit a C
  exact (congrArg (fun k => unit a C ≫ k)
    ((LabelRestriction.functor a).map_id (object a C))).trans (Category.comp_id _)

/-- The actual adjunction counit is the whole extension of the original identity functor. -/
theorem counit_app (D : FixedObjects O) :
    (adjunction a).counit.app D = desc a (LabelRestriction.object a D) (𝟙 _) := rfl

/-- Every counit generator is evaluated through its original Hom map and both image equalities. -/
theorem counit_generator (D : FixedObjects O) (x y : O) :
    Presentations.generator (quiver a (LabelRestriction.object a D))
      (relations a (LabelRestriction.object a D)) x y ≫
      homMap ((adjunction a).counit.app D) x y =
        imageMap a (LabelRestriction.object a D) (𝟙 _) x y :=
  generator_desc a (LabelRestriction.object a D) (𝟙 _) x y

/-- The counit preserves the complete original enriched composition on every target-label triple. -/
theorem counit_composition (D : FixedObjects O) (x y z : O) :
    compositionMap ((functor a).obj ((LabelRestriction.functor a).obj D)) x y z ≫
      homMap ((adjunction a).counit.app D) x z =
        (homMap ((adjunction a).counit.app D) x y ⊗ₘ
          homMap ((adjunction a).counit.app D) y z) ≫ compositionMap D x y z :=
  compositionMap_homMap ((adjunction a).counit.app D) x y z

/-- The whole original left triangle is retained by the constructed adjunction. -/
theorem left_triangle (C : FixedObjects A) :
    (functor a).map (unit a C) ≫
      (adjunction a).counit.app ((functor a).obj C) = 𝟙 ((functor a).obj C) := by
  rw [← unit_app]
  exact (adjunction a).left_triangle_components C

/-- The whole original right triangle is retained by the constructed adjunction. -/
theorem right_triangle (D : FixedObjects O) :
    unit a ((LabelRestriction.functor a).obj D) ≫
      (LabelRestriction.functor a).map ((adjunction a).counit.app D) =
        𝟙 ((LabelRestriction.functor a).obj D) := by
  rw [← unit_app]
  exact (adjunction a).right_triangle_components D

end CategoryTheory.SimplicialEnrichment.FixedObjects.LabelPushforward
