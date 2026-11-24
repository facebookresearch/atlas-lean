/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Int.ModEq
import Mathlib.Tactic.Ring

/-! # A divisibility step for powers of negative two -/

namespace MetaMathlibExt

@[expose] public section

/-- **Divisibility of $1 - (-2)^{3k}$ from $1 - (-2)^k$.** For every integer $n$ and every
natural number $k$, if $3n$ divides $1 - (-2)^k$, then $9n$ divides $1 - (-2)^{3k}$.

Since $3$ always divides $1 - (-2)^k$, this is equivalent to: if $n$ divides
$(1 - (-2)^k)/3$, then $3n$ divides $(1 - (-2)^{3k})/3$. The paper states it for positive $n$
and $k$.

Source: Dana Neidmann, *Exact Covering System Digraphs of Degree 2 and Non-Standard
Binary Representations of Integers*, INTEGERS 26 (2026), Article A107, Lemma 2
(`integers-2026-A107-lem-2`). -/
theorem three_mul_dvd_one_sub_neg_two_pow_cube (n : ℤ) (k : ℕ)
    (h : 3 * n ∣ 1 - (-2) ^ k) : 9 * n ∣ 1 - (-2) ^ (3 * k) := by
  let u : ℤ := (-2) ^ k
  have hu : (1 : ℤ) ≡ u [ZMOD 3] := by
    simpa [u] using (show (1 : ℤ) ≡ -2 [ZMOD 3] by decide).pow k
  have hone : (1 : ℤ) ≡ 1 [ZMOD 3] := Int.ModEq.refl _
  have hsum : (3 : ℤ) ≡ 1 + u + u ^ 2 [ZMOD 3] := by
    simpa using (hone.add hu).add (hu.pow 2)
  have hz : (0 : ℤ) ≡ 3 [ZMOD 3] := by decide
  have hthree : (3 : ℤ) ∣ 1 + u + u ^ 2 := by
    simpa only [sub_zero] using Int.modEq_iff_dvd.mp (hz.trans hsum)
  rw [Nat.mul_comm 3 k, pow_mul]
  change 9 * n ∣ 1 - u ^ 3
  have hproduct : (3 * n) * 3 ∣ (1 - u) * (1 + u + u ^ 2) := mul_dvd_mul h hthree
  convert hproduct using 1 <;> ring

end

end MetaMathlibExt
