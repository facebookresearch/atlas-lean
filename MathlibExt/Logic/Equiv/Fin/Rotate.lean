/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Author: @toskua
module

public import Mathlib.Logic.Equiv.Fin.Rotate
public import Mathlib.Algebra.Group.End

/-!
# A full cycle of finite rotations

For `n : ℕ`, the rotation `finRotate(n+1)` of `Fin(n+1)` satisfies `finRotate(n+1)^(n+1) = 1`.
This includes the identity rotation of `Fin 1`.
-/

@[expose] public section

open Fin.NatCast in
/-- For every `n : ℕ`, the cyclic permutation `finRotate(n+1)` of `Fin(n+1)` satisfies
`finRotate(n+1)^(n+1) = 1` in its permutation group. For `n=0`, this is the identity
permutation of `Fin 1`. -/
theorem finRotate_pow_succ (n : ℕ) : finRotate (n + 1) ^ (n + 1) = 1 := by
  have h (j : ℕ) (i : Fin (n + 1)) :
      (finRotate (n + 1) ^ j) i = i + (j : Fin (n + 1)) := by
    induction j with
    | zero => simp
    | succ j ih =>
      simp only [pow_succ', Equiv.Perm.mul_apply, ih, finRotate_apply,
        Nat.cast_succ, add_assoc]
  apply Equiv.ext
  intro i
  rw [h]
  simp
