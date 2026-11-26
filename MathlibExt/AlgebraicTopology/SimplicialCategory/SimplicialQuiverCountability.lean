/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.Combinatorics.Quiver.CountablePaths
import MathlibExt.AlgebraicTopology.SimplicialSet.CountableSimplices
import MathlibExt.AlgebraicTopology.SimplicialCategory.Presentation

/-!
# Countability of the whole original free and presented simplicial Homs

Countable original vertices and generating simplices give countably many
entire original paths at every scalar degree. The actual whole original
Hom quotient remains countable, for any original relation family and its
full simplicial closure. Neither original objects nor maps are replaced.
-/

noncomputable section
universe u
open CategoryTheory

namespace CategoryTheory.SimplicialQuiver

variable {O : Type u} [Countable O] (Q : Data O)
variable [∀ x y, (Q.Hom x y).CountableSimplices]

/-- The SAME full original generating paths are countable at every scalar degree and original pair. -/
theorem path_countable (q : SimplexCategoryᵒᵖ) (x y : O) : Countable (Path Q q x y) := by
  let _ : Quiver O := quiverAt Q q
  have (a b : O) : Countable ((Q.Hom a b).obj q) := inferInstance
  exact Quiver.Path.countable_original_paths x y

/-- Every complete original free Hom has countably many actual simplices in each degree. -/
instance freeHom_countableSimplices (x y : O) : (freeHom Q x y).CountableSimplices where
  countable_obj q := path_countable Q q x y

/-- Every whole original presented Hom quotient has countably many original simplices, with ANY actual relation
family retained. -/
instance presentedHom_countableSimplices (R : Relations Q) (x y : O) :
    (presentedHom R x y).CountableSimplices where
  countable_obj q := by
    have : Countable (Path Q q x y) := path_countable Q q x y
    change Countable (_root_.Quotient (congruence R q x y))
    infer_instance

end CategoryTheory.SimplicialQuiver
