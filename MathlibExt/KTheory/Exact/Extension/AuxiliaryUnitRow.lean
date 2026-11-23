/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Exact.Extension.Fiber

/-!
# The generic unit row of the auxiliary extension category

The original unit row is `0 → X → X`, with the given quotient retained.
This declaration is used by generic iterated localization and by the
projective auxiliary convolution. Its construction requires only the
original exact-category assumptions and independent object/Hom universes.
-/

universe u v

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.ExactCategory Limits ZeroObject

namespace AlgebraicKTheory.AuxiliaryExtension

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C] {X : C}

/-- The literal unit row of the convolution is 0→X→X at the same given quotient. -/
def unitRow (X : C) : FixedTargetExtension C X where
  A := 0
  B := X
  i := 0
  p := 𝟙 X
  zero := by simp
  admissible := by exact isAdmissibleExact_zero_id (isZero_zero C)

end AlgebraicKTheory.AuxiliaryExtension

end
