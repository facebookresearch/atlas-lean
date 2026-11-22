/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Group.Nat.Defs

/-! # Dyadic blocks of natural numbers -/

namespace MetaMathlibExt

/-- **Equal quotients by a power of two lie in one dyadic block.** Let $i$ be a natural number
and let $z < z'$ be natural numbers. Then $\lfloor z / 2^i \rfloor = \lfloor z' / 2^i \rfloor$ if
and only if there is a natural number $d$ with $d \cdot 2^i \le z$ and $z' < (d + 1) \cdot 2^i$.

Source: Ryohei Miyadera, Hikaru Manabe and Aditi Singh, *Generalizations of
Two-Dimensional and Three-Dimensional Chocolate Bar Games*, INTEGERS 25 (2025),
Article G3, Lemma 8 (a) (`integers-2025-G3-lem-8`). -/
public theorem div_two_pow_eq_iff_exists_block {z z' i : ℕ} (hzz' : z < z') :
    z / 2 ^ i = z' / 2 ^ i ↔ ∃ d, d * 2 ^ i ≤ z ∧ z' < (d + 1) * 2 ^ i := by
  constructor
  · intro h
    refine ⟨z / 2 ^ i, Nat.div_mul_le_self z _, ?_⟩
    rw [h]
    exact (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos i)).mp (Nat.lt_succ_self _)
  · rintro ⟨d, hlo, hhi⟩
    calc
      z / 2 ^ i = d := Nat.div_eq_of_lt_le hlo (Nat.lt_trans hzz' hhi)
      _ = z' / 2 ^ i := (Nat.div_eq_of_lt_le (Nat.le_trans hlo (Nat.le_of_lt hzz')) hhi).symm

end MetaMathlibExt
