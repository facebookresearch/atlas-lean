/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Data.Nat.Digits.Reverse
import Mathlib.Data.Nat.ModEq

/-!
# Divisibility under digit reversal
-/

public section

namespace MathlibExt.NumberTheory.Digits.ReverseDivisorWanted

/-- When the base squares to one modulo `n`, reversing a digit list of length `k`
multiplies its value by `B ^ (k + 1)` modulo `n`. -/
private theorem ofDigits_reverse_modEq {B n : ℕ} (hsq : B ^ 2 ≡ 1 [MOD n]) (l : List ℕ) :
    Nat.ofDigits B l.reverse ≡ B ^ (l.length + 1) * Nat.ofDigits B l [MOD n] := by
  induction l with
  | nil => simp [Nat.ModEq]
  | cons d l ih =>
    rw [Nat.ofDigits_reverse_cons]
    calc
      _ ≡ B ^ (l.length + 1) * Nat.ofDigits B l + B ^ l.length * d [MOD n] := ih.add_right _
      _ = B ^ l.length * Nat.ofDigits B (d :: l) := by
        rw [Nat.ofDigits_cons, pow_succ, Nat.mul_add, Nat.mul_assoc, Nat.add_comm]
      _ ≡ B ^ ((d :: l).length + 1) * Nat.ofDigits B (d :: l) [MOD n] := by
        rw [List.length_cons, Nat.add_assoc, pow_add]
        simpa only [mul_one] using (hsq.symm.mul_left (B ^ l.length)).mul_right
          (Nat.ofDigits B (d :: l))

/-- **In base $B$, divisors of $B^2 - 1$ divide reversals of their multiples.** Let $B \ge 2$ be
a natural number and let $n$ be a natural number dividing $B^2 - 1$. Then $n$ divides the
base-$B$ reversal of every multiple of $n$.

Source: Mohamed Ayad and Rachid Bouchenna, "Which
Integer Divides the Reverse of Any of Its Multiples?",
Proposition 5. -/
theorem dvd_reverseDigits_of_dvd (B n : ℕ) (hB : 2 ≤ B)
    (hn : n ∣ B ^ 2 - 1) (m : ℕ) (hm : n ∣ m) :
    n ∣ Nat.reverseDigits B m := by
  have hsq : B ^ 2 ≡ 1 [MOD n] :=
    ((Nat.modEq_iff_dvd' (Nat.one_le_pow _ B (by omega))).mpr hn).symm
  have hrev := ofDigits_reverse_modEq hsq (B.digits m)
  rw [Nat.ofDigits_digits] at hrev
  exact (hrev.dvd_iff dvd_rfl).mpr (dvd_mul_of_dvd_right hm _)

end MathlibExt.NumberTheory.Digits.ReverseDivisorWanted
