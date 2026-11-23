/-
Copyright (c) 2026 Avocado. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-
Modified for Atlas library integration. Standalone author labels were removed;
source attributions are retained in NOTICE.
-/
module

public import MathlibExt.Topology.Category.TopCat.PointQuotient

/-!
# Point quotients of topological pairs

This file specializes the arbitrary-arrow point quotient to topological pairs
and packages the canonical comparison map of pairs.
-/

@[expose] public section

open CategoryTheory

universe u

namespace TopPair

local notation "forgetToArrow" => MorphismProperty.Arrow.forget _ _ _

/-- The pointed quotient of a topological pair, functorial in pair maps. -/
noncomputable def pointQuotientFunctor : TopPair.{u} ⥤ PointedTopCat.{u} :=
  forgetToArrow ⋙ TopCat.pointQuotientFunctor

@[simp]
lemma pointQuotientFunctor_obj_right (P : TopPair.{u}) :
    (pointQuotientFunctor.obj P).right =
      TopCat.pointQuotient ((forgetToArrow).obj P) := rfl

@[simp]
lemma pointQuotientFunctor_obj_hom (P : TopPair.{u}) :
    (pointQuotientFunctor.obj P).hom =
      TopCat.pointQuotientPoint ((forgetToArrow).obj P) := rfl

@[simp]
lemma pointQuotientFunctor_map_right {P Q : TopPair.{u}} (f : P ⟶ Q) :
    (pointQuotientFunctor.map f).right =
      TopCat.pointQuotientMap ((forgetToArrow).map f) := rfl

/-- The pair consisting of a point quotient and its distinguished point. -/
noncomputable def pointQuotientPairFunctor : TopPair.{u} ⥤ TopPair.{u} :=
  pointQuotientFunctor ⋙ PointedTopCat.pointedPair

@[simp]
lemma pointQuotientPairFunctor_obj_fst (P : TopPair.{u}) :
    (pointQuotientPairFunctor.obj P).fst =
      TopCat.pointQuotient ((forgetToArrow).obj P) := rfl

@[simp]
lemma pointQuotientPairFunctor_obj_snd (P : TopPair.{u}) :
    (pointQuotientPairFunctor.obj P).snd = TopCat.of PUnit := rfl

@[simp]
lemma pointQuotientPairFunctor_obj_map (P : TopPair.{u}) :
    (pointQuotientPairFunctor.obj P).map =
      TopCat.pointQuotientPoint ((forgetToArrow).obj P) := rfl

@[simp]
lemma pointQuotientPairFunctor_map_fst {P Q : TopPair.{u}} (f : P ⟶ Q) :
    TopPair.Hom.fst (pointQuotientPairFunctor.map f) =
      TopCat.pointQuotientMap ((forgetToArrow).map f) := rfl

@[simp]
lemma pointQuotientPairFunctor_map_snd {P Q : TopPair.{u}} (f : P ⟶ Q) :
    TopPair.Hom.snd (pointQuotientPairFunctor.map f) = 𝟙 _ := rfl

/-- The canonical map from a pair to its pointed quotient pair. -/
noncomputable def pointQuotientComparison :
    Functor.id TopPair.{u} ⟶ pointQuotientPairFunctor where
  app P := TopPair.ofHom
    (TopCat.pointQuotientProjection.app ((forgetToArrow).obj P))
    (TopCat.isTerminalPUnit.from P.snd)
    (TopCat.pointQuotient_condition ((forgetToArrow).obj P)).symm
  naturality P Q f := by
    apply MorphismProperty.Arrow.Hom.ext
    · change TopPair.Hom.snd f ≫ TopCat.isTerminalPUnit.from Q.snd =
        TopCat.isTerminalPUnit.from P.snd ≫ 𝟙 _
      simp
    · change TopPair.Hom.fst f ≫
          TopCat.pointQuotientProjection.app ((forgetToArrow).obj Q) =
        TopCat.pointQuotientProjection.app ((forgetToArrow).obj P) ≫
          TopCat.pointQuotientMap ((forgetToArrow).map f)
      exact TopCat.pointQuotientProjection.naturality
        ((forgetToArrow).map f)

@[simp]
lemma pointQuotientComparison_app_fst (P : TopPair.{u}) :
    TopPair.Hom.fst (pointQuotientComparison.app P) =
      TopCat.pointQuotientProjection.app ((forgetToArrow).obj P) := rfl

@[simp]
lemma pointQuotientComparison_app_snd (P : TopPair.{u}) :
    TopPair.Hom.snd (pointQuotientComparison.app P) =
      TopCat.isTerminalPUnit.from P.snd := rfl

end TopPair
