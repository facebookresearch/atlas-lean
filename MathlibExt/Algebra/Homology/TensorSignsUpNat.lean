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

Koszul signs define a sign structure on `ComplexShape.up ℕ`. The first-factor degree supplies
the sign in tensor totalization of nonnegative cochain complexes.
-/

/-
Authorship of the adapted portions: @junekim623, Muse, Joël Riou.
-/

@[expose] public section

namespace ComplexShape

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The canonical Koszul tensor signs for nonnegative cochain complexes. -/
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

/-- The cochain tensor sign in degree `n` is `(-1)^n`. -/
@[simp]
lemma ε_up_ℕ (n : ℕ) : (up ℕ).ε n = (-1 : ℤˣ) ^ n := rfl

end ComplexShape
