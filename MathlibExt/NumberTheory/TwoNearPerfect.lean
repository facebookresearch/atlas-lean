/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Data.Int.Basic
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Square values of the discriminant `2 ^ (2 * k + 2) + 2 ^ (k + 2) - 2 ^ (a + 2) - 7`

If the discriminant is the square of an integer, then `k = a = 1`.
-/

namespace MetaMathlibExt

-- No integer square lies strictly between `t ^ 2` and `(t + 1) ^ 2`.
private theorem not_isSquare_of_between_consec_sq {D t : ℤ} (ht : 0 ≤ t)
    (hlo : t ^ 2 < D) (hhi : D < (t + 1) ^ 2) : ¬ IsSquare D := by
  rintro ⟨r, rfl⟩
  have h1 : |t| < |r| := sq_lt_sq.mp (by simpa only [pow_two] using hlo)
  have h2 : |r| < t + 1 :=
    abs_lt_of_sq_lt_sq (by simpa only [pow_two] using hhi) (by omega)
  rw [abs_of_nonneg ht] at h1
  omega

/-- **Square values of the discriminant $2^{2k+2} + 2^{k+2} - 2^{a+2} - 7$.** Let $a$ and $k$ be
natural numbers with $1 \le a \le k$. If $2^{2k+2} + 2^{k+2} - 2^{a+2} - 7$ is the square of an
integer, then $k = a = 1$.

Source: Vedant Aryan, Dev Madhavani, Savan Parikh, Ingrid Slattery and Joshua Zelinsky,
*On 2-Near Perfect Numbers*, INTEGERS 24 (2024), Article A61, Lemma 2
(`integers-2024-A61-lem-2`). -/
public theorem eq_one_of_isSquare_discriminant {a k : ℕ} (ha : 0 < a) (hak : a ≤ k)
    (hD : IsSquare ((2 : ℤ) ^ (2 * k + 2) + 2 ^ (k + 2) - 2 ^ (a + 2) - 7)) :
    k = 1 ∧ a = 1 := by
  have hsq : (2 : ℤ) ^ (2 * k + 2) = ((2 : ℤ) ^ (k + 1)) ^ 2 := by
    rw [show 2 * k + 2 = (k + 1) * 2 from by ring, pow_mul]
  have h2k : (2 : ℤ) ^ (k + 2) = 2 * (2 : ℤ) ^ (k + 1) := by
    rw [show k + 2 = (k + 1) + 1 from by ring, pow_succ]
    ring
  have h2pos : (0 : ℤ) < 2 ^ (a + 2) := pow_pos (show (0 : ℤ) < 2 from by norm_num) _
  rcases eq_or_lt_of_le hak with rfl | hlt
  · by_cases ha1 : a = 1
    · exact ⟨ha1, ha1⟩
    · have ha2 : 1 < a := by omega
      have h4 : (4 : ℤ) < 2 ^ (a + 1) := by
        have h := pow_lt_pow_right₀ (show (1 : ℤ) < 2 from one_lt_two)
          (show 2 < a + 1 from by omega)
        rwa [show (2 : ℤ) ^ 2 = 4 from by norm_num] at h
      have hexp : ((2 : ℤ) ^ (a + 1) - 1) ^ 2 =
          ((2 : ℤ) ^ (a + 1)) ^ 2 - 2 * 2 ^ (a + 1) + 1 := by ring
      have hlo : ((2 : ℤ) ^ (a + 1) - 1) ^ 2 <
          (2 : ℤ) ^ (2 * a + 2) + 2 ^ (a + 2) - 2 ^ (a + 2) - 7 := by
        rw [hsq, h2k, hexp]
        linarith
      have hhi : (2 : ℤ) ^ (2 * a + 2) + 2 ^ (a + 2) - 2 ^ (a + 2) - 7 <
          ((2 : ℤ) ^ (a + 1) - 1 + 1) ^ 2 := by
        rw [show ((2 : ℤ) ^ (a + 1) - 1 + 1) = (2 : ℤ) ^ (a + 1) from by ring, hsq, h2k]
        linarith
      have ht : (0 : ℤ) ≤ 2 ^ (a + 1) - 1 := by omega
      exact absurd hD (not_isSquare_of_between_consec_sq ht hlo hhi)
  · have hk2 : 1 < k := by omega
    have hak1 : a + 2 ≤ k + 1 := by omega
    have hpow : (2 : ℤ) ^ (a + 2) ≤ 2 ^ (k + 1) :=
      pow_le_pow_right₀ (show (1 : ℤ) ≤ 2 from by norm_num) hak1
    have hu8 : (8 : ℤ) ≤ 2 ^ (k + 1) := by
      have h := pow_le_pow_right₀ (show (1 : ℤ) ≤ 2 from by norm_num)
        (show 3 ≤ k + 1 from by omega)
      rwa [show (2 : ℤ) ^ 3 = 8 from by norm_num] at h
    have hexp : ((2 : ℤ) ^ (k + 1) + 1) ^ 2 =
        ((2 : ℤ) ^ (k + 1)) ^ 2 + 2 * 2 ^ (k + 1) + 1 := by ring
    have hlo : ((2 : ℤ) ^ (k + 1)) ^ 2 <
        (2 : ℤ) ^ (2 * k + 2) + 2 ^ (k + 2) - 2 ^ (a + 2) - 7 := by
      rw [hsq, h2k]
      linarith
    have hhi : (2 : ℤ) ^ (2 * k + 2) + 2 ^ (k + 2) - 2 ^ (a + 2) - 7 <
        ((2 : ℤ) ^ (k + 1) + 1) ^ 2 := by
      rw [hsq, h2k, hexp]
      linarith
    have ht : (0 : ℤ) ≤ 2 ^ (k + 1) := pow_nonneg (show (0 : ℤ) ≤ 2 from by norm_num) _
    exact absurd hD (not_isSquare_of_between_consec_sq ht hlo hhi)

end MetaMathlibExt
