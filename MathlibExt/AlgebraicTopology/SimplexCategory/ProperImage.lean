/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module
public import Mathlib.AlgebraicTopology.SimplexCategory.Basic

/-!
# Proper images of ordinal maps

A monomorphism of the simplex category that is not an epimorphism raises the degree, so the image
of a map that is not an epimorphism has strictly lower degree than its target.
-/

@[expose] public section

noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped Simplicial
namespace SimplexCategory

/-- An original monic nonsurjective ordinal map has strictly lower source degree. -/
theorem len_lt_of_mono_of_not_epi {A B : SimplexCategory} (f : A ⟶ B) [Mono f] (hf : ¬ Epi f) :
    A.len < B.len :=
  len_lt_of_mono f fun h => hf (by subst h; rw [eq_id_of_mono f]; infer_instance)

/-- The SAME genuine original image of every nonsurjective ordinal lies in a strictly lower
degree. -/
theorem image_len_lt_of_not_epi {A B : SimplexCategory} (f : A ⟶ B) (hf : ¬ Epi f) :
    (image f).len < B.len := by
  apply len_lt_of_mono_of_not_epi (image.ι f)
  intro h
  let _ : Epi (image.ι f) := h
  apply hf
  rw [← image.fac f]
  infer_instance

end SimplexCategory
