/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Order.MinMax

/-! # Dyadic blocks of natural numbers -/

namespace MetaMathlibExt

/-- **Taking a minimum preserves quotients by powers of two.** Let $a, b, c, k \in \mathbb{N}$. If
$\lfloor a / 2^k \rfloor = \lfloor b / 2^k \rfloor$, then
$\lfloor \min(a, c) / 2^k \rfloor = \lfloor \min(b, c) / 2^k \rfloor$.

Source: Ryohei Miyadera, Hikaru Manabe and Aditi Singh, *Generalizations of
Two-Dimensional and Three-Dimensional Chocolate Bar Games*, INTEGERS 25 (2025),
Article G3, Lemma 2 (i) (`integers-2025-G3-lem-2`). -/
public theorem min_div_two_pow_eq_of_div_two_pow_eq {a b k : ℕ}
    (hab : a / 2 ^ k = b / 2 ^ k) (c : ℕ) :
    min a c / 2 ^ k = min b c / 2 ^ k := by
  have hmono : Monotone (fun n : ℕ ↦ n / 2 ^ k) := fun _ _ h ↦ Nat.div_le_div_right h
  simp only [hmono.map_min, hab]

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

/-- **Dyadic splitting of two numbers with different quotients.** Let $z, z', i$ be natural
numbers with $\lfloor z / 2^i \rfloor < \lfloor z' / 2^i \rfloor$. Then there are natural numbers
$c$, $s$ and $t$ with $s \ge i$, $t < 2^s$, $z = c \cdot 2^{s+1} + t$ and
$c \cdot 2^{s+1} + 2^s \le z'$.

Source: Ryohei Miyadera, Hikaru Manabe and Aditi Singh, *Generalizations of
Two-Dimensional and Three-Dimensional Chocolate Bar Games*, INTEGERS 25 (2025),
Article G3, Lemma 8 (b) (`integers-2025-G3-lem-8`). -/
public theorem exists_split_of_div_two_pow_lt {z z' i : ℕ}
    (h : z / 2 ^ i < z' / 2 ^ i) :
    ∃ c s t : ℕ, i ≤ s ∧ t < 2 ^ s ∧ z = c * 2 ^ (s + 1) + t ∧
      c * 2 ^ (s + 1) + 2 ^ s ≤ z' := by
  let q := z / 2 ^ i
  by_cases he : 2 ∣ q
  · -- An even quotient places z in the lower half of the block at the next scale.
    have hbase : q / 2 * 2 ^ (i + 1) = q * 2 ^ i := by
      rw [Nat.pow_succ, Nat.mul_comm (2 ^ i), ← Nat.mul_assoc, Nat.div_mul_cancel he]
    refine ⟨q / 2, i, z % 2 ^ i, Nat.le_refl i, Nat.mod_lt _ (Nat.two_pow_pos i), ?_, ?_⟩
    · rw [hbase, Nat.mul_comm q]
      exact (Nat.div_add_mod z _).symm
    · rw [hbase, ← Nat.succ_mul]
      exact (Nat.le_div_iff_mul_le (Nat.two_pow_pos i)).mp h
  · -- Halving an odd quotient preserves its strict inequality with the larger quotient.
    have hnext : z / 2 ^ (i + 1) < z' / 2 ^ (i + 1) := by
      rw [Nat.pow_succ, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul]
      dsimp only [q] at he
      omega
    obtain ⟨c, s, t, hs, hsplit⟩ := exists_split_of_div_two_pow_lt hnext
    exact ⟨c, s, t, Nat.le_of_succ_le hs, hsplit⟩
termination_by z' / 2 ^ i
decreasing_by
  rw [Nat.pow_succ, ← Nat.div_div_eq_div_mul]
  exact Nat.div_lt_self (Nat.zero_lt_of_lt h) (by decide)

end MetaMathlibExt
