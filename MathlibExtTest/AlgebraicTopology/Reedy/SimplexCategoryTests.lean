/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.AlgebraicTopology.Reedy.SimplexCategory

/-!
# Tests for the simplex-category Reedy structure
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty
open HomotopicalAlgebra
open scoped Simplicial

namespace MathlibExtTest.SimplexCategoryReedy

example : ReedyStructure (epimorphisms SimplexCategory)
    (monomorphisms SimplexCategory) ℕ :=
  SimplexCategory.reedyStructure

example (X : SimplexCategory) :
    SimplexCategory.reedyStructure.deg X = X.len :=
  rfl

example {X Y : SimplexCategory} (f : X ⟶ Y) [Epi f]
    (hf : ¬ identities SimplexCategory f) : Y.len < X.len :=
  SimplexCategory.reedyStructure.lt₁ f (by infer_instance) hf

example {X Y : SimplexCategory} (f : X ⟶ Y) [Mono f]
    (hf : ¬ identities SimplexCategory f) : X.len < Y.len :=
  SimplexCategory.reedyStructure.lt₂ f (by infer_instance) hf

example {X Y : SimplexCategory} (f : X ⟶ Y) :
    SimplexCategory.reedyStructure.degHom f = (image f).len := by
  let h : (epimorphisms SimplexCategory).MapFactorizationData
      (monomorphisms SimplexCategory) f :=
    .mk (image f) (factorThruImage f) (image.ι f) (image.fac f)
    (by infer_instance) (by infer_instance)
  simpa only [SimplexCategory.reedyStructure] using
    SimplexCategory.reedyStructure.degHom_eq h

example {X Y : SimplexCategory} (f : X ⟶ Y) :
    Nonempty (Unique
      ((epimorphisms SimplexCategory).MapFactorizationData
        (monomorphisms SimplexCategory) f)) :=
  SimplexCategory.reedyStructure.nonempty_unique f

example : SimplexCategory.reedyStructure.deg ⦋0⦌ = 0 := rfl
example : SimplexCategory.reedyStructure.deg ⦋3⦌ = 3 := rfl

#print axioms SimplexCategory.reedyStructure

end MathlibExtTest.SimplexCategoryReedy
