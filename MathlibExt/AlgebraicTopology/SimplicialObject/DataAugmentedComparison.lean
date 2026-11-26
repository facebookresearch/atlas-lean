/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.AlgebraicTopology.SimplicialObject.ToAugmented

/-!
# Equality of augmented simplicial data conversions

For augmented simplicial data X in a category C, both the functorial conversion and the direct
conversion give an augmented simplicial object with diagram X.left.toSimplicialObject and
augmentation point X.right. Their augmentation transformations agree as well.

Consequently, the two conversions yield equal augmented objects, with the same diagram, point
and map. The object and morphism universes of C are independent.
-/

@[expose] public section

open CategoryTheory

universe v u

namespace CategoryTheory.SimplicialObject.Data.Augmented

variable {C : Type u} [Category.{v} C]

/-- Equality of functorial and direct augmented-data conversions.

For augmented simplicial data X, applying toSimplicialFunctor to X yields
X.toSimplicialAugmented. The equality preserves the converted simplicial diagram, augmentation
point and entire augmentation transformation. -/
@[simp] theorem toSimplicialFunctor_obj_eq (X : Augmented C) :
    (toSimplicialFunctor (C := C)).obj X = X.toSimplicialAugmented := by
  have hhom : ((toSimplicialFunctor (C := C)).obj X).hom =
      X.toSimplicialAugmented.hom :=
    toSimplicialFunctor_obj_hom X
  exact congrArg
    (fun f : X.left.toSimplicialObject ⟶ (SimplicialObject.const C).obj X.right =>
      ({ left := X.left.toSimplicialObject, right := X.right, hom := f } :
        SimplicialObject.Augmented C)) hhom

end CategoryTheory.SimplicialObject.Data.Augmented

end
