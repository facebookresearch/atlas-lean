/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Data.Nat.GCD.Basic
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.NumberTheory.Divisors
public import MathlibExt.NumberTheory.Recurrences.SylvesterSequence
import Mathlib.Algebra.Divisibility.Basic
import Mathlib.Algebra.Group.Monoid
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Set.Defs
import Mathlib.Data.Set.Insert
import Mathlib.Data.Set.Operations

/-!
# Mersenne numbers in the Sylvester sequence

The Sylvester numbers of the form `2 ^ r - 1` with `r ≥ 1` are exactly `3` and `7`.

## References

* Abderrahim Makki Naciri, *A Note on Sylvester's Sequence*, INTEGERS 24
  (2024), Article A117, Corollary 1(a).
  <https://math.colgate.edu/~integers/y117/y117.pdf>
-/

@[expose] public section

namespace MathlibExt.NumberTheory.Recurrences.SylvesterSequenceWanted

private theorem sylvester_mod_one_mod_seven (n : ℕ) (hn : 3 ≤ n) :
    sylvesterNumber n % 7 = 1 := by
  change sylvesterNumber n ≡ 1 [MOD 7]
  induction n, hn using Nat.le_induction with
  | base => decide
  | succ n _ ih =>
    calc
      sylvesterNumber (n + 1) = sylvesterNumber n ^ 2 - sylvesterNumber n + 1 :=
        Nat.generalizedSylvester_succ 1 n
      _ ≡ 1 ^ 2 - 1 + 1 [MOD 7] :=
        (Nat.ModEq.sub (Nat.le_self_pow two_ne_zero _) (by decide)
          (ih.pow 2) ih).add_right 1
      _ ≡ 1 [MOD 7] := by decide

private theorem three_dvd_of_mersenne_mod (r : ℕ)
    (h36 : (2 ^ r - 1) % 36 = 7) : 3 ∣ r := by
  have h9 : (2 ^ r - 1) % 9 = 7 := by omega
  have h1 : 1 ≤ 2 ^ r := Nat.one_le_two_pow
  have h8mod : (2 ^ r) % 9 = 8 := by omega
  have h8 : (2 ^ r : ℕ) ≡ 8 [MOD 9] := h8mod
  have hr : r = 6 * (r / 6) + r % 6 := (Nat.div_add_mod r 6).symm
  have hpow : 2 ^ r = (2 ^ 6) ^ (r / 6) * 2 ^ (r % 6) := by
    conv_lhs => rw [hr]
    rw [pow_add, pow_mul]
  have h61 : (2 ^ 6 : ℕ) ≡ 1 [MOD 9] := by decide
  have h6 : ((2 ^ 6) ^ (r / 6) : ℕ) ≡ 1 [MOD 9] := by
    simpa using h61.pow (r / 6)
  have hmul : ((2 ^ 6) ^ (r / 6) * 2 ^ (r % 6) : ℕ) ≡ 2 ^ (r % 6) [MOD 9] := by
    simpa using h6.mul (Nat.ModEq.refl (2 ^ (r % 6)))
  have hr_eq : (2 ^ r : ℕ) ≡ 2 ^ (r % 6) [MOD 9] := by
    rw [hpow]
    exact hmul
  have hk : (2 ^ (r % 6) : ℕ) ≡ 8 [MOD 9] := hr_eq.symm.trans h8
  have hcases : r % 6 = 0 ∨ r % 6 = 1 ∨ r % 6 = 2 ∨ r % 6 = 3 ∨ r % 6 = 4 ∨
      r % 6 = 5 := by omega
  rcases hcases with h | h | h | h | h | h
  · rw [h] at hk
    exact absurd hk (by decide)
  · rw [h] at hk
    exact absurd hk (by decide)
  · rw [h] at hk
    exact absurd hk (by decide)
  · omega
  · rw [h] at hk
    exact absurd hk (by decide)
  · rw [h] at hk
    exact absurd hk (by decide)

private theorem seven_dvd_two_pow_sub_one_of_three_dvd (r : ℕ) (h : 3 ∣ r) :
    7 ∣ 2 ^ r - 1 := by
  have h73 : (2 ^ 3 - 1 : ℕ) = 7 := rfl
  have hdvd : (2 ^ 3 - 1 : ℕ) ∣ 2 ^ r - 1 :=
    (Nat.pow_sub_one_dvd_pow_sub_one_iff (by decide : 1 < 2)).mpr h
  simpa [h73] using hdvd

/-- **Mersenne numbers in the Sylvester sequence.** Let $(S_n)_{n \ge 0}$ be the Sylvester
sequence, $S_0 = 2$ and $S_{n+1} = S_n^2 - S_n + 1$. The natural numbers $x$ such that $x = S_n$
for some $n$ and $x = 2^r - 1$ for some $r \ge 1$ are exactly $3$ and $7$.

Source: Abderrahim Makki Naciri, "A Note on Sylvester's Sequence", Corollary 1(a). -/
public theorem mersenne_sylvester_values_eq :
    {x : ℕ | ∃ n r : ℕ, 1 ≤ r ∧ x = sylvesterNumber n ∧
      x = 2 ^ r - 1} = {3, 7} := by
  apply Set.ext
  intro x
  simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨n, r, hr, rfl, hx⟩
    by_cases hn3 : n < 3
    · have h012 : n = 0 ∨ n = 1 ∨ n = 2 := by omega
      rcases h012 with rfl | rfl | rfl
      · have h0 : sylvesterNumber 0 = 2 := rfl
        rw [h0] at hx
        have h1 : 1 ≤ 2 ^ r := Nat.one_le_two_pow
        have h3 : 2 ^ r = 3 := by omega
        have hr0 : r ≠ 0 := by omega
        have hdvd : 2 ∣ 2 ^ r := dvd_pow_self 2 hr0
        rw [h3] at hdvd
        exact absurd hdvd (by decide)
      · have h1 : sylvesterNumber 1 = 3 := rfl
        rw [h1]
        exact Or.inl rfl
      · have h2 : sylvesterNumber 2 = 7 := rfl
        rw [h2]
        exact Or.inr rfl
    · have hn3' : 3 ≤ n := by omega
      have h36 : sylvesterNumber n % 36 = 7 :=
        sylvester_modEq_seven_mod_thirty_six n (by omega)
      rw [hx] at h36
      have h3dvd : 3 ∣ r := three_dvd_of_mersenne_mod r h36
      have h7dvd : 7 ∣ 2 ^ r - 1 :=
        seven_dvd_two_pow_sub_one_of_three_dvd r h3dvd
      rw [← hx] at h7dvd
      have h71 : sylvesterNumber n % 7 = 1 :=
        sylvester_mod_one_mod_seven n hn3'
      have h70 : sylvesterNumber n % 7 = 0 := Nat.mod_eq_zero_of_dvd h7dvd
      exact absurd (h71.symm.trans h70) (by decide)
  · rintro (rfl | rfl)
    · exact ⟨1, 2, by decide, rfl, rfl⟩
    · exact ⟨2, 3, by decide, rfl, rfl⟩

end MathlibExt.NumberTheory.Recurrences.SylvesterSequenceWanted
