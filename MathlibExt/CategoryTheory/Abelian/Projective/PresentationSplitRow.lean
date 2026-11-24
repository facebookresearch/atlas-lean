/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Author: @toskua
module
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Abelian.Basic

/-!
## The split middle presentation of the degree-one horseshoe sign test
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

namespace CategoryTheory.ProjectiveResolution
variable {C : Type u} [Category.{v} C] [Abelian C]

/--
The middle presentation uses the negative left coordinate required by the original augmentation
equation.
-/
def presentationMiddleRow (S : ShortComplex C) : ShortComplex C :=
  ShortComplex.mk (biprod.lift (-𝟙 S.X₁) S.f)
    (biprod.desc S.f (𝟙 S.X₂)) (by simp)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- This middle augmentation row splits by the negative first projection and original right inclusion. -/
def presentationMiddleRowSplitting (S : ShortComplex C) : (presentationMiddleRow S).Splitting where
  r := -biprod.fst
  s := biprod.inr
  f_r := by dsimp [presentationMiddleRow]; simp
  s_g := by dsimp [presentationMiddleRow]; simp
  id := by
    apply biprod.hom_ext' <;> apply biprod.hom_ext <;>
        simp [presentationMiddleRow, Category.assoc, Preadditive.comp_add,
      Preadditive.add_comp]

/-- The middle row is genuinely short exact, with its original stored objects/maps. -/
theorem presentationMiddleRow_shortExact (S : ShortComplex C) :
    (presentationMiddleRow S).ShortExact := (presentationMiddleRowSplitting S).shortExact

end CategoryTheory.ProjectiveResolution
