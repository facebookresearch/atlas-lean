/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Recurrences.CRecursiveModModRepresentation
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.Tactic.Linarith

/-! # Tests for the sign-dependent double remainder -/

namespace MetaMathlibExt.exists_mod_mod_representation_sign

open Polynomial Finset

-- The constant sequence 1 has generating function 1/(1-X). Base 3 works at every
-- positive index, including n = 1. The leading coefficient -1 gives no offset.
example : ∃ r : ℕ, 3 ≤ r ∧ ∀ n : ℕ, 1 ≤ n →
    ((r : ℤ) ^ (n ^ 2) * (r : ℤ) ^ n) % ((r : ℤ) ^ n - 1) % (r : ℤ) ^ n = 1 := by
  let B : Polynomial ℤ := 1 - X
  have hd : B.natDegree = 1 := by
    rw [show B = 1 - X from rfl, natDegree_sub_eq_right_of_natDegree_lt (by simp)]
    simp
  have hr : B.reverse = X - 1 := by simp [reverse, hd, B, reflect_sub]
  have h1 : (1 : Polynomial ℤ).reverse = 1 := by simp [reverse]
  have hgf : PowerSeries.mk (fun _ => (1 : ℤ)) * (B : PowerSeries ℤ) = 1 := by
    simpa [B, Pi.one_def] using PowerSeries.mk_one_mul_one_sub_eq_one ℤ
  obtain ⟨r, h3, h⟩ := MetaMathlibExt.exists_mod_mod_representation_sign
    (fun _ => 1) 1 B 3 (by simp [B]) (by simp [hd]) one_ne_zero (by simpa using hgf) (by
      intro n hn
      have hn0 : n ≠ 0 := by omega
      let q : ℤ := 3 ^ n
      have hq : 3 ≤ q := le_self_pow₀ (by decide) hn0
      have hq' : (3 : ℚ) ≤ q := by exact_mod_cast hq
      have hden : 0 < (q : ℚ) - 1 := by linarith
      have hf : ⌊(q : ℚ) ^ (n + 1) / ((q : ℚ) - 1)⌋ = ∑ i ∈ range (n + 1), q ^ i := by
        rw [Int.floor_eq_iff, le_div_iff₀ hden, div_lt_iff₀ hden]
        push_cast
        have := geom_sum_mul (q : ℚ) (n + 1)
        constructor <;> linarith
      have hmod : (∑ i ∈ range (n + 1), q ^ i) % q = 1 := by
        rw [geom_sum_succ, Int.mul_add_emod_self_left, Int.emod_eq_of_lt (by decide) (by omega)]
      rw [← hf] at hmod
      have hnum : (3 : ℚ) ^ (n ^ 2) * 3 ^ n = (q : ℚ) ^ (n + 1) := by
        simp [q, pow_succ, ← pow_mul]
      rw [h1, hr]
      simp only [hd, natDegree_one, Nat.sub_zero, mul_one, eval_one, eval_sub, eval_X,
        Nat.cast_one, Int.cast_one, Int.cast_sub, Nat.cast_ofNat, hnum]
      exact hmod.symm)
  refine ⟨r, h3, fun n hn => ?_⟩
  have hα : B.reverse.coeff 0 = -1 := by simp [hr]
  have he := (h n hn).symm
  rw [hα, hr, h1] at he
  norm_num [hd] at he
  exact_mod_cast he

-- The series 1/(1-2X²) starts 1, 0, 2. Multiplying numerator and denominator by
-- 1-3X gives leading coefficient +6, so even the zero term requires a nonzero residue.
example : let q : ℤ := 8
    (-(q ^ 1 * q ^ 2 * (q - 3))) % ((q ^ 2 - 2) * (q - 3)) % q = 6 := by decide

example : let q : ℤ := 8 ^ 2
    (-(q ^ 2 * q ^ 2 * (q - 3))) % ((q ^ 2 - 2) * (q - 3)) % q = 6 * (2 + 1) := by decide

end MetaMathlibExt.exists_mod_mod_representation_sign
