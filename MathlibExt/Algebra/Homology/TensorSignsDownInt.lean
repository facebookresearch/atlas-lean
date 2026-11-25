/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
  Author: @toskua, Avocado
-/
module

public import Mathlib.Algebra.Homology.ComplexShapeSigns

@[expose] public section

namespace ComplexShape

/-- Signs for `down ℤ` (Mathlib provides `down ℕ` and `up ℤ` only):
enables `TotalComplexShape (down ℤ) (down ℤ) (down ℤ)`. -/
instance : TensorSigns (down ℤ) where
  ε' := MonoidHom.mk' (fun n : Multiplicative ℤ => (n.toAdd).negOnePow)
    (fun x y => Int.negOnePow_add x.toAdd y.toAdd)
  rel_add p q r (hpq : q + 1 = p) := by
    change q + r + 1 = p + r
    lia
  add_rel p q r (hpq : q + 1 = p) := by
    change r + q + 1 = r + p
    lia
  ε'_succ := by
    rintro _ q rfl
    change (q : ℤ).negOnePow = -((q + 1 : ℤ)).negOnePow
    rw [Int.negOnePow_succ, neg_neg]

@[simp]
lemma ε_down_ℤ (n : ℤ) : (ComplexShape.down ℤ).ε n = n.negOnePow := rfl

end ComplexShape
