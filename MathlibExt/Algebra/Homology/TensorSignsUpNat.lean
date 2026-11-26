/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.Algebra.Homology.ComplexShapeSigns

/-!
# Tensor signs for nonnegative cochain complexes

For nonnegative cochain complexes, the degree sign ε(n) = (−1)^n determines the tensor
differential d(x⊗y) = dx⊗y + (−1)^p x⊗dy for x in degree p. The signs are multiplicative under
degree addition and change sign when the cochain degree increases by one.
-/

/-
Authorship of the adapted portions: @junekim623, Muse, Joël Riou.
-/

@[expose] public section

namespace ComplexShape

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The nonnegative cochain shape on ℕ has tensor signs ε(n) = (−1)^n in ℤˣ. They satisfy ε(p+q) =
ε(p)ε(q) and ε(p+1) = −ε(p), giving the signed tensor differential d(x⊗y) = dx⊗y + (−1)^p x⊗dy
in bidegree (p,q). -/
instance tensorSignsUpNat : (up ℕ).TensorSigns where
  ε' := MonoidHom.mk' (fun (i : ℕ) => (-1 : ℤˣ) ^ i)
    (pow_add (-1 : ℤˣ))
  rel_add p q r (hpq : p + 1 = q) := by
    dsimp
    omega
  add_rel p q r (hpq : p + 1 = q) := by
    dsimp
    omega
  ε'_succ := by
    rintro p _ rfl
    dsimp
    rw [pow_add, pow_one, mul_neg, mul_one]

/-- For every natural number n, the tensor sign of the nonnegative cochain shape is ε(n) = (−1)^n as
a unit of ℤ. This is the coefficient multiplying the second-factor differential when the first
factor is in degree n. -/
@[simp]
lemma ε_up_ℕ (n : ℕ) : (up ℕ).ε n = (-1 : ℤˣ) ^ n := rfl

end ComplexShape
