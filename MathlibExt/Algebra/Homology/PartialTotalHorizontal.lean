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
# Horizontal components of the first-quadrant total differential

Let `B` be a first-quadrant bicomplex in a preadditive category with finite coproducts. In the
homological total complex, the horizontal component from `(p + 1, q)` to `(p, q)` has
coefficient `ε₁ = 1`. It is the horizontal bicomplex differential followed by the inclusion of
`(p, q)` in total degree `p + q`.

At column zero the horizontal component vanishes, since zero has no predecessor in the
natural-index complex shape.
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

/-- Successor horizontal total component has coefficient one.

For natural `p` and `q`, the horizontal part `B.d₁ (.down ℕ) (p + 1) q (p + q)` equals `(B.d
(p + 1) p).f q` followed by the inclusion of `B.X p q` in total degree `p + q`. The total-
complex horizontal sign is `ε₁ = 1`. -/
theorem d₁_succ_eq_horizontal (p q : ℕ) :
    B.d₁ (ComplexShape.down ℕ) (p + 1) q (p + q) =
      (B.d (p + 1) p).f q ≫
        B.ιTotal (ComplexShape.down ℕ) p q (p + q) rfl := by
  have hε₁ : (ComplexShape.down ℕ).ε₁ (ComplexShape.down ℕ)
      (ComplexShape.down ℕ) (p + 1, q) = 1 := rfl
  rw [HomologicalComplex₂.d₁_eq B (ComplexShape.down ℕ)
    (show (ComplexShape.down ℕ).Rel (p + 1) p by rfl)
    q (p + q) rfl, hε₁, one_smul]

/-- Horizontal total component at column zero is zero.

For every natural `q` and total degree `n`, `B.d₁ (.down ℕ) 0 q n = 0`. The horizontal chain
shape has no arrow from column zero to a predecessor. -/
theorem d₁_zero_eq_zero (q n : ℕ) :
    B.d₁ (ComplexShape.down ℕ) 0 q n = 0 := by
  apply HomologicalComplex₂.d₁_eq_zero
  intro h
  change (ComplexShape.down ℕ).next 0 + 1 = 0 at h
  omega

end HomologicalComplex₂

end
