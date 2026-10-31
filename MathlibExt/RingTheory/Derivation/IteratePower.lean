/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0

Adapted from https://github.com/anthropics/formal-math
at commit 16a5ce41304fcdaea4e0be7c132e1c361dc26da5,
eth/proof/rates/GeneralPieces/Series/Deriv.lean.
-/

/- Modifications copyright (c) Meta Platforms, Inc. and affiliates. -/
module

public import Mathlib.RingTheory.Derivation.Basic

/-!
# Iterated derivations of powers

This file gives a closed formula for iterating a derivation on powers of an element whose
derivative is a scalar multiple of its square.
-/

@[expose] public section

namespace Derivation

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

private theorem apply_pow_of_apply_eq_smul_sq (D : Derivation R A A) {r : R} {epsilon : A}
    (h : D epsilon = r • epsilon ^ 2) (m : ℕ) :
    D (epsilon ^ m) = (r * (m : R)) • epsilon ^ (m + 1) := by
  rcases m with _ | m
  · simp
  · rw [D.leibniz_pow, h, Nat.add_sub_cancel, smul_eq_mul, mul_smul_comm, ← pow_add,
      ← Nat.cast_smul_eq_nsmul R, smul_smul, mul_comm r]

/-- If `D epsilon = r • epsilon²`, then the `n`th iterate of `D` on `epsilon^m` has
coefficient `r^n` times the ascending factorial of `m`. The coefficient is not cancelled,
so the formula remains valid in positive characteristic. -/
theorem iterate_pow_of_apply_eq_smul_sq (D : Derivation R A A) (r : R) (epsilon : A)
    (h : D epsilon = r • epsilon ^ 2) (n m : ℕ) :
    (D : A → A)^[n] (epsilon ^ m) =
      (r ^ n * (m.ascFactorial n : R)) • epsilon ^ (m + n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, D.map_smul,
      apply_pow_of_apply_eq_smul_sq D h, smul_smul, Nat.ascFactorial_succ]
    push_cast
    congr 1
    ring

end Derivation
