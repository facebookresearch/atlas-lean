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

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.Single
public import Mathlib.Algebra.Homology.HomologicalBicomplex

/-!
# Two horizontal rows with zero vertical differential

Both rows are the degree-zero single complex on Q. The horizontal differential is a specified
map of those rows, and all remaining horizontal objects are zero. Identity and zero choices
give actual fixtures for the connecting sign and the stable quotient, respectively.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

namespace MathlibExtTest.Algebra.Homology.TwoRowFixture

/-- The degree-zero vertical row on Q, with zero vertical differential. -/
def verticalRow : ChainComplex (ModuleCat ℚ) ℕ :=
  (ChainComplex.single₀ (ModuleCat ℚ)).obj (ModuleCat.of ℚ ℚ)

/-- A genuine two-row bicomplex, with its specified horizontal differential. -/
def twoRows (f : verticalRow ⟶ verticalRow) :
    HomologicalComplex₂ (ModuleCat ℚ) (ComplexShape.down ℕ) (ComplexShape.down ℕ) :=
  ChainComplex.mk verticalRow verticalRow 0 f 0 (by simp)
    (fun S => ⟨0, 0, by simp⟩)

/-- The horizontal identity fixture used to detect the connecting sign. -/
def horizontalIdentity := twoRows (𝟙 verticalRow)

/-- The horizontal-zero fixture used for a proper abutment image inclusion. -/
def horizontalZero := twoRows 0

example (f : verticalRow ⟶ verticalRow) : (twoRows f).X 0 = verticalRow := rfl

example (f : verticalRow ⟶ verticalRow) : (twoRows f).X 1 = verticalRow := rfl

example (f : verticalRow ⟶ verticalRow) : (twoRows f).d 1 0 = f := by
  exact ChainComplex.mk_d_1_0 _ _ _ _ _ _ _

end MathlibExtTest.Algebra.Homology.TwoRowFixture
