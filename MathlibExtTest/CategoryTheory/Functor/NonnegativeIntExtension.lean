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

public import MathlibExt.CategoryTheory.Functor.NonnegativeIntExtension

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace CategoryTheory.Functor

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
  [HasZeroObject C]
  (F : ℕ ⥤ C)

example : ℤ ⥤ C :=
  nonnegativeIntExtension F

example (z : ℤ) (hz : 0 ≤ z) :
    (nonnegativeIntExtension F).obj z ≅ F.obj z.toNat :=
  nonnegativeIntObjIso F z hz

example (z : ℤ) (hz : z < 0) :
    IsZero ((nonnegativeIntExtension F).obj z) :=
  isZero_nonnegativeIntObj_of_neg F z hz

example {a b : ℤ} (h : a ≤ b) :
    (nonnegativeIntExtension F).map (homOfLE h) =
      nonnegativeIntMap F h :=
  nonnegativeIntExtension_map F h

example {a b : ℤ} (h : a ≤ b) (ha : 0 ≤ a) :
    (nonnegativeIntObjIso F a ha).inv ≫
        (nonnegativeIntExtension F).map (homOfLE h) =
      F.map (homOfLE (Int.toNat_le_toNat h)) ≫
        (nonnegativeIntObjIso F b (ha.trans h)).inv :=
  nonnegativeIntExtension_objIso_inv_comp_map F h ha

example {a b : ℤ} (h : a ≤ b) (ha : a < 0) :
    (nonnegativeIntExtension F).map (homOfLE h) = 0 :=
  nonnegativeIntMap_eq_zero_of_neg F h ha

example (n : ℕ) :
    (nonnegativeIntExtension F).obj (n : ℤ) ≅ F.obj n := by
  simpa using nonnegativeIntObjIso F (n : ℤ) (Int.natCast_nonneg n)

end CategoryTheory.Functor

end
