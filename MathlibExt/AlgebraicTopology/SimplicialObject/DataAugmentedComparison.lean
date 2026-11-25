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
# Agreement of the two augmented data conversions

The functorial conversion and the direct augmented-object conversion have the
same diagram and point. Their augmentation maps agree by the native computation
lemma, including the identity introduced by the comma-category map.
-/

@[expose] public section

open CategoryTheory

universe v u

namespace CategoryTheory.SimplicialObject.Data.Augmented

variable {C : Type u} [Category.{v} C]

/-- The functorial and direct conversions give the same actual augmented object. -/
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
