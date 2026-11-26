/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Data.Nat.Digits.Reverse
import Mathlib.Data.List.Basic

/-!
# Basic decimal reverse divisors

The two basic families have a block of nines between the two digits at each end.
Reading these digit lists in both directions gives their lengths and reversal quotients.
-/

set_option autoImplicit false

public section

namespace MathlibExt.NumberTheory.Digits.ReverseDivisorWanted

private theorem ofDigits_replicate_nine (r : ℕ) (tail : List ℕ) :
    Nat.ofDigits 10 (List.replicate r 9 ++ tail) + 1 =
      10 ^ r * (Nat.ofDigits 10 tail + 1) := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [List.replicate_succ, List.cons_append, Nat.ofDigits_cons, pow_succ', mul_assoc, ← ih]
    omega

/-- Evaluate a decimal digit list with two digits on either side of a block of nines. -/
private theorem ofDigits_nine_block (r a b c d : ℕ) :
    Nat.ofDigits 10 ([a, b] ++ List.replicate r 9 ++ [c, d]) + 100 =
      a + 10 * b + 10 ^ (r + 2) * (c + 10 * d + 1) := by
  have h : Nat.ofDigits 10 (List.replicate r 9 ++ [c, d]) + 1 =
      10 ^ r * (c + 10 * d + 1) := by
    simpa only [Nat.ofDigits_cons, Nat.ofDigits_nil, mul_zero, add_zero]
      using ofDigits_replicate_nine r [c, d]
  change Nat.ofDigits 10 (a :: b :: (List.replicate r 9 ++ [c, d])) + 100 = _
  rw [Nat.ofDigits_cons, Nat.ofDigits_cons, pow_add, mul_right_comm, ← h]
  omega

private theorem digits_of_nine_block (r a b c d : ℕ)
    (ha : a < 10) (hb : b < 10) (hc : c < 10) (hd : d < 10) (hd0 : d ≠ 0) :
    Nat.digits 10 (Nat.ofDigits 10 ([a, b] ++ List.replicate r 9 ++ [c, d])) =
      [a, b] ++ List.replicate r 9 ++ [c, d] := by
  apply Nat.digits_ofDigits 10 (by decide)
  · intro i hi
    simp only [List.mem_append, List.mem_cons, List.mem_replicate, List.not_mem_nil,
      or_false] at hi
    omega
  · intro h
    simpa [← List.append_assoc, List.getLast_append_of_right_ne_nil] using hd0

/-- **Basic reverse divisors.** For every natural number $k \ge 2$, the numbers
$11(10^k - 1)$ and $22(10^k - 1)$ both have exactly $k + 2$ decimal digits, the decimal
reversal of $11(10^k - 1)$ equals $9 \cdot 11(10^k - 1)$, and the decimal reversal of
$22(10^k - 1)$ equals $4 \cdot 22(10^k - 1)$.

Source: Mohamed Ayad and Rachid Bouchenna, "Which
Integer Divides the Reverse of Any of Its Multiples?",
Theorem 1 (quoted from the literature). -/
theorem basic_reverseDivisors (k : ℕ) (hk : 2 ≤ k) :
    (Nat.digits 10 (11 * (10 ^ k - 1))).length = k + 2 ∧
      Nat.reverseDigits 10 (11 * (10 ^ k - 1)) =
        9 * (11 * (10 ^ k - 1)) ∧
      (Nat.digits 10 (22 * (10 ^ k - 1))).length = k + 2 ∧
      Nat.reverseDigits 10 (22 * (10 ^ k - 1)) =
        4 * (22 * (10 ^ k - 1)) := by
  obtain ⟨r, rfl⟩ : ∃ r, k = r + 2 := ⟨k - 2, by omega⟩
  have hpow : 1 ≤ (10 : ℕ) ^ (r + 2) := Nat.pow_pos (by decide)
  have h11 : Nat.ofDigits 10 ([9, 8] ++ List.replicate r 9 ++ [0, 1]) =
      11 * (10 ^ (r + 2) - 1) := by
    have h := ofDigits_nine_block r 9 8 0 1
    omega
  have h22 : Nat.ofDigits 10 ([8, 7] ++ List.replicate r 9 ++ [1, 2]) =
      22 * (10 ^ (r + 2) - 1) := by
    have h := ofDigits_nine_block r 8 7 1 2
    omega
  have hd11 := digits_of_nine_block r 9 8 0 1
    (by decide) (by decide) (by decide) (by decide) (by decide)
  have hd22 := digits_of_nine_block r 8 7 1 2
    (by decide) (by decide) (by decide) (by decide) (by decide)
  rw [h11] at hd11
  rw [h22] at hd22
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hd11]
    simp only [List.length_append, List.length_replicate, List.length_cons, List.length_nil]
    omega
  · rw [Nat.reverseDigits, hd11, List.reverse_append, List.reverse_append,
      List.reverse_replicate]
    change Nat.ofDigits 10 ([1, 0] ++ List.replicate r 9 ++ [8, 9]) = _
    have h := ofDigits_nine_block r 1 0 8 9
    omega
  · rw [hd22]
    simp only [List.length_append, List.length_replicate, List.length_cons, List.length_nil]
    omega
  · rw [Nat.reverseDigits, hd22, List.reverse_append, List.reverse_append,
      List.reverse_replicate]
    change Nat.ofDigits 10 ([2, 1] ++ List.replicate r 9 ++ [7, 8]) = _
    have h := ofDigits_nine_block r 2 1 7 8
    omega

end MathlibExt.NumberTheory.Digits.ReverseDivisorWanted
