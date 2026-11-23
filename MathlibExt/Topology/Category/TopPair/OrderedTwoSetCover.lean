/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.TopCat.OrderedTwoSetCover
public import MathlibExt.Topology.Category.TopPair.Excision

/-!
# Ordered two-set covers — pair/excision diagram

Coefficient-independent pair and excision diagram associated to ordered two-set covers.
-/

@[expose] public section

open CategoryTheory

universe w

namespace AlgebraicTopology.OrderedTwoSetCover

/-- The pair `(B, A ∩ B)` associated to an ordered two-set cover. -/
noncomputable def rightInterPairFunctor : OrderedTwoSetCover.{w} ⥤ TopPair.{w} where
  obj C := TopPair.excisionSource C.X C.left C.right
  map {C D} f := TopPair.ofHom (rightFunctor.map f) (interFunctor.map f) (by
    apply TopCat.hom_ext
    ext x
    rfl)
  map_id C := by ext <;> rfl
  map_comp f g := by ext <;> rfl

/-- The pair `(X, A)` associated to an ordered two-set cover. -/
noncomputable def spaceLeftPairFunctor : OrderedTwoSetCover.{w} ⥤ TopPair.{w} where
  obj C := TopPair.excisionTarget C.X C.left
  map {C D} f := TopPair.ofHom (spaceFunctor.map f) (leftFunctor.map f) (by
    apply TopCat.hom_ext
    ext x
    rfl)
  map_id C := by ext <;> rfl
  map_comp f g := by ext <;> rfl

/-- Excision morphisms `(B, A ∩ B) ⟶ (X, A)`, natural in ordered covers. -/
noncomputable def excisionNatTrans :
    rightInterPairFunctor.{w} ⟶ spaceLeftPairFunctor.{w} where
  app C := TopPair.excisionHom C.X C.left C.right
  naturality C D f := by
    ext <;> rfl

@[simp]
lemma rightInterPairFunctor_obj (C : OrderedTwoSetCover.{w}) :
    rightInterPairFunctor.obj C = TopPair.excisionSource C.X C.left C.right := rfl

@[simp]
lemma spaceLeftPairFunctor_obj (C : OrderedTwoSetCover.{w}) :
    spaceLeftPairFunctor.obj C = TopPair.excisionTarget C.X C.left := rfl

@[simp]
lemma excisionNatTrans_app (C : OrderedTwoSetCover.{w}) :
    excisionNatTrans.app C = TopPair.excisionHom C.X C.left C.right := rfl

end AlgebraicTopology.OrderedTwoSetCover
