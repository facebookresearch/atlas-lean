/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.Digits.ReverseDivisor
import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic.NormNum

/-!
# Palindromes with property $P^*$

A positive decimal palindrome with property $P^*$ is one of $1$, $3$, $9$, $11$, $33$, and $99$.

Source: Mohamed Ayad and Rachid Bouchenna, "Which Integer Divides the Reverse of Any of Its
Multiples?", *INTEGERS* 25 (2025), Article A37, Proposition 3
(<https://math.colgate.edu/~integers/vol25.html>).
-/

@[expose] public section

namespace MathlibExt.NumberTheory.Digits.ReverseDivisorWanted

private theorem reverse_modEq (n : ℕ) (hn : 0 < n) (h : HasPropertyPStar n)
    (l₁ l₂ : List ℕ) (hlen : l₁.length = l₂.length)
    (hd₁ : ∀ d ∈ l₁, d < 10) (hd₂ : ∀ d ∈ l₂, d < 10)
    (hne₁ : l₁ ≠ []) (hne₂ : l₂ ≠ [])
    (hlast₁ : l₁.getLast hne₁ ≠ 0) (hlast₂ : l₂.getLast hne₂ ≠ 0)
    (hab : Nat.ofDigits 10 l₁ ≡ Nat.ofDigits 10 l₂ [MOD n]) :
    Nat.ofDigits 10 l₁.reverse ≡ Nat.ofDigits 10 l₂.reverse [MOD n] := by
  let k := (Nat.digits 10 n).length
  let r := n - (Nat.ofDigits 10 l₁ * 10 ^ k) % n
  have hr : r ≤ n := Nat.sub_le _ _
  have hrlen : (Nat.digits 10 r).length ≤ k :=
    (Nat.digits_length_le_iff (by decide) r).mpr
      (hr.trans_lt (Nat.lt_base_pow_length_digits (by decide)))
  let s := Nat.digits 10 r ++ List.replicate (k - (Nat.digits 10 r).length) 0
  have hslen : s.length = k := by simp [s, Nat.add_sub_of_le hrlen]
  have hsval : Nat.ofDigits 10 s = r := by simp [s, Nat.ofDigits_digits]
  have hsd : ∀ d ∈ s, d < 10 := by
    intro d hd
    simp only [s, List.mem_append, List.mem_replicate] at hd
    rcases hd with hd | ⟨_, rfl⟩
    · exact Nat.digits_lt_base (by decide) hd
    · decide
  have hdiv₁ : n ∣ Nat.ofDigits 10 (s ++ l₁) := by
    rw [Nat.ofDigits_append, hslen, hsval, Nat.modEq_zero_iff_dvd.symm]
    change (r + 10 ^ k * Nat.ofDigits 10 l₁) % n = 0 % n
    have hrem := Nat.mod_lt (Nat.ofDigits 10 l₁ * 10 ^ k) hn
    calc
      (r + 10 ^ k * Nat.ofDigits 10 l₁) % n =
          (r + (Nat.ofDigits 10 l₁ * 10 ^ k) % n) % n := by
            simp [Nat.add_mod, Nat.mul_comm]
      _ = n % n := by rw [Nat.sub_add_cancel hrem.le]
      _ = 0 % n := by simp
  have hdiv₂ : n ∣ Nat.ofDigits 10 (s ++ l₂) := by
    rw [Nat.ofDigits_append, hslen, hsval]
    apply (((hab.mul_left (10 ^ k)).add_left r).dvd_iff dvd_rfl).mp
    simpa [Nat.ofDigits_append, hslen, hsval] using hdiv₁
  have rev (l : List ℕ) (hd : ∀ d ∈ l, d < 10) (hne : l ≠ [])
      (hlast : l.getLast hne ≠ 0) :
      Nat.reverseDigits 10 (Nat.ofDigits 10 (s ++ l)) =
        Nat.ofDigits 10 l.reverse + 10 ^ l.length * Nat.ofDigits 10 s.reverse := by
    rw [Nat.reverseDigits, Nat.digits_ofDigits 10 (by decide)]
    · simp [Nat.ofDigits_append]
    · intro d hmem
      rcases List.mem_append.mp hmem with hmem | hmem
      · exact hsd d hmem
      · exact hd d hmem
    · intro hne'
      simpa only [List.getLast_append_of_right_ne_nil s l hne] using hlast
  have hrev₁ := h _ hdiv₁
  have hrev₂ := h _ hdiv₂
  rw [rev l₁ hd₁ hne₁ hlast₁] at hrev₁
  rw [rev l₂ hd₂ hne₂ hlast₂, ← hlen] at hrev₂
  exact Nat.ModEq.add_right_cancel (Nat.ModEq.refl _)
    (hrev₁.modEq_zero_nat.trans hrev₂.zero_modEq_nat)

private theorem palindrome_dvd (n : ℕ) (hn : 0 < n)
    (hpal : Nat.reverseDigits 10 n = n) (h : HasPropertyPStar n) : n ∣ 99 := by
  have hne : Nat.digits 10 n ≠ [] := Nat.digits_ne_nil_iff_ne_zero.mpr hn.ne'
  let ds := (Nat.digits 10 n).dropLast
  let d := (Nat.digits 10 n).getLast hne
  have hdigits : Nat.digits 10 n = ds ++ [d] :=
    (List.dropLast_append_getLast hne).symm
  have hdpos : 0 < d := Nat.pos_of_ne_zero (Nat.getLast_digit_ne_zero 10 hn.ne')
  have hdlt : d < 10 := Nat.digits_lt_base (by decide) (List.getLast_mem hne)
  have hds : ∀ a ∈ ds, a < 10 := by
    intro a ha
    exact Nat.digits_lt_base (by decide) (by rw [hdigits]; simp [ha])
  have hnval : n = Nat.ofDigits 10 ds + 10 ^ ds.length * d := by
    rw [← Nat.ofDigits_digits 10 n, hdigits, Nat.ofDigits_append, Nat.ofDigits_singleton]
  have hnrev : n = d + 10 * Nat.ofDigits 10 ds.reverse := by
    simpa [Nat.reverseDigits, hdigits, Nat.ofDigits_append, Nat.ofDigits_cons] using hpal.symm
  let l₁ := List.replicate ds.length 0 ++ [10 - d, 1]
  let l₂ := ds ++ [0, 2]
  have hlen : l₁.length = l₂.length := by simp [l₁, l₂]
  have hd₁ : ∀ a ∈ l₁, a < 10 := by
    intro a ha
    simp only [l₁, List.mem_append, List.mem_replicate, List.mem_cons,
      List.not_mem_nil, or_false] at ha
    rcases ha with ⟨_, rfl⟩ | rfl | rfl <;> omega
  have hd₂ : ∀ a ∈ l₂, a < 10 := by
    intro a ha
    simp only [l₂, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with ha | rfl | rfl
    · exact hds a ha
    · decide
    · decide
  have hne₁ : l₁ ≠ [] := by simp [l₁]
  have hne₂ : l₂ ≠ [] := by simp [l₂]
  have hlast₁ : l₁.getLast hne₁ ≠ 0 := by simp [l₁]
  have hlast₂ : l₂.getLast hne₂ ≠ 0 := by simp [l₂]
  have hsum : Nat.ofDigits 10 l₂ = Nat.ofDigits 10 l₁ + n := by
    simp only [l₁, l₂, Nat.ofDigits_append, Nat.ofDigits_replicate_zero,
      List.length_replicate, Nat.ofDigits_cons, Nat.ofDigits_nil, mul_zero, add_zero,
      zero_add, mul_one]
    have hsub : 10 - d + d = 10 := Nat.sub_add_cancel hdlt.le
    rw [hnval]
    simp only [Nat.mul_add]
    have hmul : 10 ^ ds.length * (10 - d) + 10 ^ ds.length * d =
        10 ^ ds.length * 10 := by rw [← Nat.mul_add, hsub]
    omega
  have hab : Nat.ofDigits 10 l₁ ≡ Nat.ofDigits 10 l₂ [MOD n] := by
    rw [hsum]
    exact Nat.ModEq.refl _ |>.add (dvd_rfl.zero_modEq_nat)
  have hr := reverse_modEq n hn h l₁ l₂ hlen hd₁ hd₂ hne₁ hne₂ hlast₁ hlast₂ hab
  have hcarry : Nat.ofDigits 10 l₂.reverse + 99 = Nat.ofDigits 10 l₁.reverse + 10 * n := by
    simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
      List.cons_append, Nat.ofDigits_cons, zero_add, List.reverse_replicate,
      Nat.ofDigits_replicate_zero, mul_zero, add_zero, l₂, l₁]
    have hsub : 10 - d + d = 10 := Nat.sub_add_cancel hdlt.le
    rw [hnrev]
    omega
  have hmod : 99 ≡ 10 * n [MOD n] :=
    Nat.ModEq.add_left_cancel (Nat.ModEq.refl (Nat.ofDigits 10 l₁.reverse))
      (by simpa only [hcarry] using hr.add_right 99)
  exact Nat.modEq_zero_iff_dvd.mp (hmod.trans (dvd_mul_left n 10).modEq_zero_nat)

/-- **Palindromes with property $P^*$.** Let $n \ge 1$ be a natural number that is a decimal
palindrome, that is, whose decimal reversal equals $n$. If $n$ has the property $P^*$, then $n$
is one of $1$, $3$, $9$, $11$, $33$ and $99$.

Source: Mohamed Ayad and Rachid Bouchenna, "Which
Integer Divides the Reverse of Any of Its Multiples?",
Proposition 3. -/
theorem palindrome_hasPropertyPStar (n : ℕ) (hn : 1 ≤ n)
    (hpal : Nat.reverseDigits 10 n = n) (h : HasPropertyPStar n) :
    n = 1 ∨ n = 3 ∨ n = 9 ∨ n = 11 ∨ n = 33 ∨ n = 99 := by
  have hdvd := palindrome_dvd n hn hpal h
  have hle : n ≤ 99 := Nat.le_of_dvd (by decide) hdvd
  interval_cases n <;> norm_num at hdvd
  all_goals norm_num

end MathlibExt.NumberTheory.Digits.ReverseDivisorWanted
