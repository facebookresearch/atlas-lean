/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Data.Nat.Digits.Reverse
import Mathlib.Data.Nat.Digits.Lemmas

/-! # The two families of basic reverse divisors

In both families, two fixed pairs of decimal digits surround a string of nines. Evaluating the
little-endian list and its reversal gives the advertised length and quotient.
-/

namespace MathlibExt.NumberTheory.Digits.ReverseDivisorWanted

private def digitBlock (r a b c d : ℕ) : List ℕ := [a, b] ++ (List.replicate r 9 ++ [c, d])

private theorem ofDigits_replicate_nine (r : ℕ) :
    Nat.ofDigits 10 (List.replicate r 9) + 1 = 10 ^ r := by
  induction r with
  | zero => rfl
  | succ r ih =>
      rw [List.replicate_succ, Nat.ofDigits_cons, pow_succ]
      omega

private theorem digitBlock_value (r a b c d : ℕ) :
    Nat.ofDigits 10 (digitBlock r a b c d) =
      a + 10 * b + 100 * (Nat.ofDigits 10 (List.replicate r 9) + 10 ^ r * (c + 10 * d)) := by
  simp [digitBlock, Nat.ofDigits_cons, Nat.ofDigits_append, Nat.ofDigits_nil]
  omega

private theorem digits_digitBlock (r a b c d : ℕ)
    (ha : a < 10) (hb : b < 10) (hc : c < 10) (hd : d < 10) (hd0 : d ≠ 0) :
    Nat.digits 10 (Nat.ofDigits 10 (digitBlock r a b c d)) = digitBlock r a b c d := by
  apply Nat.digits_ofDigits 10 (by decide)
  · intro i hi
    simp only [digitBlock, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with (rfl | rfl) | hi | rfl | rfl
    · exact ha
    · exact hb
    · rw [List.eq_of_mem_replicate hi]
      decide
    · exact hc
    · exact hd
  · intro h
    change ([a, b] ++ (List.replicate r 9 ++ [c, d])).getLast h ≠ 0
    rw [List.getLast_append_of_right_ne_nil _ _ (by simp),
      List.getLast_append_of_right_ne_nil _ _ (by simp)]
    simpa using hd0

private theorem digitBlock_reverse (r a b c d : ℕ) :
    (digitBlock r a b c d).reverse = digitBlock r d c b a := by
  simp [digitBlock, List.reverse_append, List.reverse_replicate, List.append_assoc]

/-- **Basic reverse divisors.** For every natural number $k \ge 2$, the numbers
$11(10^k - 1)$ and $22(10^k - 1)$ both have exactly $k + 2$ decimal digits, the decimal
reversal of $11(10^k - 1)$ equals $9 \cdot 11(10^k - 1)$, and the decimal reversal of
$22(10^k - 1)$ equals $4 \cdot 22(10^k - 1)$.

Source: Mohamed Ayad and Rachid Bouchenna, "Which
Integer Divides the Reverse of Any of Its Multiples?",
Theorem 1 (quoted from the literature). -/
public theorem basic_reverseDivisors (k : ℕ) (hk : 2 ≤ k) :
    (Nat.digits 10 (11 * (10 ^ k - 1))).length = k + 2 ∧
      Nat.reverseDigits 10 (11 * (10 ^ k - 1)) =
        9 * (11 * (10 ^ k - 1)) ∧
      (Nat.digits 10 (22 * (10 ^ k - 1))).length = k + 2 ∧
      Nat.reverseDigits 10 (22 * (10 ^ k - 1)) =
        4 * (22 * (10 ^ k - 1)) := by
  let r := k - 2
  have hkr : k = r + 2 := by dsimp [r]; omega
  have h := ofDigits_replicate_nine r
  have h11 : Nat.ofDigits 10 (digitBlock r 9 8 0 1) = 11 * (10 ^ k - 1) := by
    rw [hkr]
    simp only [digitBlock_value, pow_succ]
    omega
  have h22 : Nat.ofDigits 10 (digitBlock r 8 7 1 2) = 22 * (10 ^ k - 1) := by
    rw [hkr]
    simp only [digitBlock_value, pow_succ]
    omega
  have h9 : Nat.ofDigits 10 (digitBlock r 1 0 8 9) = 9 * (11 * (10 ^ k - 1)) := by
    rw [hkr]
    simp only [digitBlock_value, pow_succ]
    omega
  have h4 : Nat.ofDigits 10 (digitBlock r 2 1 7 8) = 4 * (22 * (10 ^ k - 1)) := by
    rw [hkr]
    simp only [digitBlock_value, pow_succ]
    omega
  have hd11 : Nat.digits 10 (11 * (10 ^ k - 1)) = digitBlock r 9 8 0 1 := by
    rw [← h11]
    exact digits_digitBlock _ _ _ _ _ (by decide) (by decide) (by decide) (by decide) (by decide)
  have hd22 : Nat.digits 10 (22 * (10 ^ k - 1)) = digitBlock r 8 7 1 2 := by
    rw [← h22]
    exact digits_digitBlock _ _ _ _ _ (by decide) (by decide) (by decide) (by decide) (by decide)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hd11]
    simp [digitBlock]
    omega
  · rw [Nat.reverseDigits, hd11, digitBlock_reverse, h9]
  · rw [hd22]
    simp [digitBlock]
    omega
  · rw [Nat.reverseDigits, hd22, digitBlock_reverse, h4]

end MathlibExt.NumberTheory.Digits.ReverseDivisorWanted
