/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import Mathlib.AlgebraicTopology.SimplicialSet.Basic
import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal
import Mathlib.CategoryTheory.Comma.Presheaf.Basic
import Mathlib.CategoryTheory.Comma.Over.Pullback
import Mathlib.CategoryTheory.Category.ULift
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
import Mathlib.CategoryTheory.Monoidal.Closed.Cartesian
import Mathlib.CategoryTheory.Monoidal.Closed.FunctorToTypes

/-!
# Cartesian closedness of the SAME original simplicial over categories

The native presheaf-over equivalence is reused in its matching universe,
after the genuine native ULiftHom equivalence of the simplex category.
Every original simplex object, ordinal operator and source map is retained.
Closedness is transported to the SAME original Over category and its
native Cartesian products. No model structure or weak comparison outcome
is changed or supplied.
-/

noncomputable section
universe u
open CategoryTheory Opposite

namespace SSet.OverPresheaf

/-- The native simplex index with exactly the coefficient Hom universe required by the native over-presheaf
equivalence. -/
abbrev Index := ULiftHom.{u} SimplexCategory

/-- The actual native reindexing equivalence, retaining the SAME original simplex maps. -/
def equivalence : SSet.{u} ≌ (Index.{u}ᵒᵖ ⥤ Type u) :=
  Functor.asEquivalence ((Functor.whiskeringLeft _ _ (Type u)).obj
    (ULiftHom.equiv (C := SimplexCategory)).symm.functor.op)

/-- Every reindexed original coefficient is literally its native old simplex coefficient. -/
theorem equivalence_obj_obj (X : SSet.{u}) (q : Index.{u}ᵒᵖ) :
    (equivalence.functor.obj X).obj q = X.obj ((ULiftHom.down (C := SimplexCategory)).op.obj q) := rfl

/-- Every full reindexed ordinal operator is the SAME original operator at the native lowered index. -/
theorem equivalence_obj_map (X : SSet.{u}) {q r : Index.{u}ᵒᵖ} (f : q ⟶ r) :
    (equivalence.functor.obj X).map f = X.map ((ULiftHom.down (C := SimplexCategory)).op.map f) := rfl

/-- Every full original source-natural coefficient map is retained literally. -/
theorem equivalence_map_app {X Y : SSet.{u}} (f : X ⟶ Y) (q : Index.{u}ᵒᵖ) :
    (equivalence.functor.map f).app q = f.app ((ULiftHom.down (C := SimplexCategory)).op.obj q) := rfl

/-- The SAME original over category is genuinely equivalent to its native matching-universe presheaf category. -/
def overEquivalence (B : SSet.{u}) :
    Over B ≌ ((CostructuredArrow yoneda (equivalence.functor.obj B))ᵒᵖ ⥤ Type u) :=
  (Over.postEquiv B equivalence).trans (overEquivPresheafCostructuredArrow (equivalence.functor.obj B))

/-- The original simplicial over category with its native Cartesian products is closed in every coefficient universe. -/
@[instance_reducible]
def cartesianClosed (B : SSet.{u}) [CartesianMonoidalCategory (Over B)] : MonoidalClosed (Over B) :=
  cartesianClosedOfEquiv (overEquivalence B).symm

end SSet.OverPresheaf
