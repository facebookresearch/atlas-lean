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

public import Mathlib.Algebra.Homology.SpectralSequence.ComplexShape
public import MathlibExt.Algebra.Homology.PartialTotalBasic

/-!
# Horizontal components of the natural total complex

For a natural first-quadrant bicomplex, the horizontal component of the total
differential carries no extra sign: the total-complex convention has
`ε₁ = 1`.  This file records the successor-row component formula and the
vanishing boundary at row zero.

Comparison with the transported page-one differential is deferred.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasFiniteCoproducts C]

local instance : HasFiniteBiproducts C :=
  HasFiniteBiproducts.of_hasFiniteCoproducts

variable (B : HomologicalComplex₂ C (ComplexShape.down ℕ)
  (ComplexShape.down ℕ))

/-- On the successor row, the horizontal component of the total differential
is the bicomplex horizontal differential followed by the target-row
inclusion.  The horizontal total-complex sign is `ε₁=1`. -/
theorem d₁_succ_eq_horizontal (p q : ℕ) :
    B.d₁ (ComplexShape.down ℕ) (p + 1) q (p + q) =
      (B.d (p + 1) p).f q ≫
        B.ιTotal (ComplexShape.down ℕ) p q (p + q) rfl := by
  have hε₁ : (ComplexShape.down ℕ).ε₁ (ComplexShape.down ℕ)
      (ComplexShape.down ℕ) (p + 1, q) = 1 := rfl
  rw [HomologicalComplex₂.d₁_eq B (ComplexShape.down ℕ)
    (show (ComplexShape.down ℕ).Rel (p + 1) p by rfl)
    q (p + q) rfl, hε₁, one_smul]

/-- The horizontal component from row zero vanishes because the natural
chain shape has no predecessor of zero. -/
theorem d₁_zero_eq_zero (q n : ℕ) :
    B.d₁ (ComplexShape.down ℕ) 0 q n = 0 := by
  apply HomologicalComplex₂.d₁_eq_zero
  intro h
  change (ComplexShape.down ℕ).next 0 + 1 = 0 at h
  omega

end HomologicalComplex₂

end
