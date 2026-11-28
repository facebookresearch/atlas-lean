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

/-- For the chain-complex shape down ℤ, the tensor sign in degree p is
ε(p) = p.negOnePow = (-1)^p, for positive and negative integers alike.
On a summand K_p ⊗ L_q in total degree p + q, this gives the differential
d_K ⊗ id + (-1)^p id ⊗ d_L. These signs supply the total-complex shape
for tensoring two integer-graded chain complexes. -/
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
