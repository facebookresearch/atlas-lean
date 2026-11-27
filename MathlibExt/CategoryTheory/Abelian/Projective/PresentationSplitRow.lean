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
# Split middle row of a presentation

For any map `f : A → B` in an abelian category, the row
`A → A ⊞ B → B` with maps `[-id,f]` and `[f,id]` is split exact.
Its retraction is `-fst` and its section is `inr`. This row supplies
the signed middle augmentation in a projective presentation horseshoe.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

namespace CategoryTheory.ProjectiveResolution
variable {C : Type u} [Category.{v} C] [Abelian C]

/-- In an abelian category `C`, a short complex `S : A → B → X`
gives the middle row `A → A ⊞ B → B` with maps
`[-𝟙 A,S.f]` and `[S.f,𝟙 B]`; their composite is zero. -/
def presentationMiddleRow (S : ShortComplex C) : ShortComplex C :=
  ShortComplex.mk (biprod.lift (-𝟙 S.X₁) S.f)
    (biprod.desc S.f (𝟙 S.X₂)) (by simp)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- In an abelian category `C`, for a short complex `S : A → B → X`,
the row with maps `[-id,S.f]`, `[S.f,id]` is split by retraction
`-biprod.fst : A ⊞ B → A` and section `biprod.inr : B → A ⊞ B`. -/
def presentationMiddleRowSplitting (S : ShortComplex C) : (presentationMiddleRow S).Splitting where
  r := -biprod.fst
  s := biprod.inr
  f_r := by dsimp [presentationMiddleRow]; simp
  s_g := by dsimp [presentationMiddleRow]; simp
  id := by
    apply biprod.hom_ext' <;> apply biprod.hom_ext <;>
        simp [presentationMiddleRow, Category.assoc, Preadditive.comp_add,
      Preadditive.add_comp]

/-- In an abelian category `C`, for any short complex
`S : A → B → X`, the row `A → A ⊞ B → B` with maps
`[-id,S.f]`, `[S.f,id]` is short exact. -/
theorem presentationMiddleRow_shortExact (S : ShortComplex C) :
    (presentationMiddleRow S).ShortExact := (presentationMiddleRowSplitting S).shortExact

end CategoryTheory.ProjectiveResolution
