/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/

module

public import MathlibExt.CategoryTheory.Functor.NonnegativeEIntExtension

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

universe v u

namespace CategoryTheory.Functor

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
  [HasZeroObject C]
  (F : ℕ ⥤ C) (X : C) (ι : F ⟶ (Functor.const ℕ).obj X)

example : EInt ⥤ C :=
  nonnegativeEIntExtension F X ι

example : (nonnegativeEIntExtension F X ι).obj ⊥ = 0 :=
  nonnegativeEIntExtension_obj_bot F X ι

example (z : ℤ) :
    (nonnegativeEIntExtension F X ι).obj (z : EInt) =
      (nonnegativeIntExtension F).obj z :=
  nonnegativeEIntExtension_obj_coe F X ι z

example : (nonnegativeEIntExtension F X ι).obj ⊤ = X :=
  nonnegativeEIntExtension_obj_top F X ι

example {a b : ℤ} (h : a ≤ b) :
    (nonnegativeEIntExtension F X ι).map
        (homOfLE (show (a : EInt) ≤ b by simpa)) =
      (nonnegativeIntExtension F).map (homOfLE h) :=
  nonnegativeEIntExtension_map_coe F X ι h

example (a : ℤ) :
    (nonnegativeEIntExtension F X ι).map
        (homOfLE (show (a : EInt) ≤ ⊤ by simp)) =
      nonnegativeIntToTopMap F X ι a :=
  nonnegativeEIntExtension_map_to_top F X ι a

example {a b : ℤ} (h : a ≤ b) :
    (nonnegativeIntExtension F).map (homOfLE h) ≫
        nonnegativeIntToTopMap F X ι b =
      nonnegativeIntToTopMap F X ι a :=
  nonnegativeIntExtension_map_comp_nonnegativeIntToTopMap F X ι h

end CategoryTheory.Functor

end
