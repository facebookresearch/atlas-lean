/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Tactic.Ring

/-! # A divisibility step for powers of two -/

namespace MetaMathlibExt

/-- **Divisibility of $2^{3n} + 1$ from $2^n + 1$.** For every natural number $n$, if $3n$
divides $2^n + 1$, then $9n$ divides $2^{3n} + 1$.

Equivalently, if $3$ divides $2^n + 1$ and $n$ divides $(2^n + 1)/3$, then $3n$ divides
$(2^{3n} + 1)/3$. For $n = 0$ the hypothesis fails, so positivity is not assumed.

Source: Dana Neidmann, *Exact Covering System Digraphs of Degree 2 and Non-Standard
Binary Representations of Integers*, INTEGERS 26 (2026), Article A107, Lemma 1
(`integers-2026-A107-lem-1`). -/
public theorem three_mul_dvd_two_pow_add_one_cube (n : ℕ) (h : 3 * n ∣ 2 ^ n + 1) :
    9 * n ∣ 2 ^ (3 * n) + 1 := by
  obtain ⟨k, hk⟩ := h
  rw [Nat.mul_comm 3 n, pow_mul]
  apply Int.ofNat_dvd.mp
  push_cast
  have hk' : (2 : ℤ) ^ n + 1 = 3 * (n : ℤ) * (k : ℤ) := by exact_mod_cast hk
  rw [eq_sub_of_add_eq hk']
  refine ⟨(k : ℤ) * (3 * ((n : ℤ) * (k : ℤ)) ^ 2 - 3 * (n : ℤ) * (k : ℤ) + 1), ?_⟩
  ring

end MetaMathlibExt
