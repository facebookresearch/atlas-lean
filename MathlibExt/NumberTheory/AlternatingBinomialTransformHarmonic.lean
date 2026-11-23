/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.NumberTheory.Harmonic.Defs
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

namespace Work

private lemma gamma_ne_zero_of_hs (s : ℂ) (hs : ∀ m : ℕ, s ≠ -((m + 1 : ℕ) : ℂ)) (t : ℕ) :
    Complex.Gamma (s + ((t : ℂ) + 1)) ≠ 0 := by
  apply Complex.Gamma_ne_zero
  intro m h
  apply hs (m + t)
  have hcast : ((m + t + 1 : ℕ) : ℂ) = (m : ℂ) + (t : ℂ) + 1 := by push_cast; ring
  have hsm : s = -((m : ℂ) + (t : ℂ) + 1) := by linear_combination h
  rw [hsm, hcast]

private lemma gamma_N_ne_zero (s : ℂ) (n : ℕ) (hs : ∀ m : ℕ, s ≠ -((m + 1 : ℕ) : ℂ)) (hn : 0 < n) :
    Complex.Gamma ((n : ℂ) + s) ≠ 0 := by
  apply Complex.Gamma_ne_zero
  intro m h
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  apply hs (m + k)
  have hcast : ((m + k + 1 : ℕ) : ℂ) = (m : ℂ) + ((k : ℕ) : ℂ) + 1 := by push_cast; ring
  have hk1 : (((k + 1 : ℕ)) : ℂ) = ((k : ℕ) : ℂ) + 1 := by push_cast; ring
  rw [hk1] at h
  have hsm : s = -((m : ℂ) + ((k : ℕ) : ℂ) + 1) := by linear_combination h
  rw [hsm, hcast]

private lemma add_ne_zero_of_hs (s : ℂ) (n : ℕ) (hs : ∀ m : ℕ, s ≠ -((m + 1 : ℕ) : ℂ)) (hn : 0 < n) :
    (s + (n : ℂ)) ≠ 0 := by
  intro h
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  apply hs k
  have hsm : s = -(((k + 1 : ℕ) : ℂ)) := by linear_combination h
  exact hsm

private lemma nat_gamma_ne_zero (t : ℕ) : Complex.Gamma ((t : ℂ) + 1) ≠ 0 := by
  rw [Complex.Gamma_nat_eq_factorial]
  exact Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero t)

private lemma gamma_add_nat_ne_zero (s : ℂ) (w : ℕ)
    (hs : ∀ m : ℕ, s ≠ -((m + 1 : ℕ) : ℂ)) (hs0 : s ≠ 0) :
    Complex.Gamma (s + (w : ℂ)) ≠ 0 := by
  apply Complex.Gamma_ne_zero
  intro m' hm'
  have hcast : (((m' + w : ℕ)) : ℂ) = (m' : ℂ) + (w : ℂ) := by push_cast; ring
  have hsm : s = -((((m' + w : ℕ)) : ℂ)) := by
    rw [hcast]
    linear_combination hm'
  rcases Nat.eq_zero_or_pos (m' + w) with h0 | hpos
  · rw [h0] at hsm
    simp at hsm
    exact hs0 hsm
  · obtain ⟨v, hv⟩ : ∃ v, m' + w = v + 1 := ⟨m' + w - 1, by omega⟩
    rw [hv] at hsm
    exact hs v hsm

/-- Ratio identity: C(N-1,t)/((t:ℂ)+1) = C(N,t+1)/N where N = n+s. -/
private lemma ratio_lemma (s : ℂ) (n t u : ℕ) (hn : n = t + 1 + u)
    (hs : ∀ m : ℕ, s ≠ -((m + 1 : ℕ) : ℂ)) :
    Complex.Gamma ((n : ℂ) + s) /
        (Complex.Gamma ((t : ℂ) + 1) * Complex.Gamma (((n : ℂ) + s) - (t : ℂ))) /
        ((t : ℂ) + 1)
      = Complex.Gamma ((((n : ℂ) + s)) + 1) /
        (Complex.Gamma ((((t + 1 : ℕ)) : ℂ) + 1) *
          Complex.Gamma (((((n : ℂ) + s)) - ((((t + 1 : ℕ)) : ℂ))) + 1)) /
        (((n : ℂ) + s)) := by
  subst hn
  have ht1 : (((t + 1 : ℕ)) : ℂ) = (t : ℂ) + 1 := by push_cast; ring
  have hcast1 : (((t + 1 + u : ℕ)) : ℂ) = (t : ℂ) + 1 + (u : ℂ) := by push_cast; ring
  have hN : ((t : ℂ) + 1 + (u : ℂ) + s) ≠ 0 := by
    have hn1 : 0 < t + 1 + u := by omega
    have hne := add_ne_zero_of_hs s (t + 1 + u) hs hn1
    rw [hcast1] at hne
    intro hc
    apply hne
    linear_combination hc
  have hNt : ((t : ℂ) + 1 + (u : ℂ) + s) - (t : ℂ) = s + ((u : ℂ) + 1) := by ring
  have hNt1 : (((t : ℂ) + 1 + (u : ℂ) + s) - ((t : ℂ) + 1)) + 1 = s + ((u : ℂ) + 1) := by ring
  rw [hcast1, ht1, hNt, hNt1]
  have hG1 : Complex.Gamma (((t : ℂ) + 1 + (u : ℂ) + s) + 1)
      = ((t : ℂ) + 1 + (u : ℂ) + s) * Complex.Gamma ((t : ℂ) + 1 + (u : ℂ) + s) :=
    Complex.Gamma_add_one _ hN
  have ht1ne : ((t : ℂ) + 1) ≠ 0 := by
    have heq : ((t : ℂ) + 1) = (((t + 1 : ℕ)) : ℂ) := by push_cast; ring
    rw [heq]
    exact Nat.cast_ne_zero.mpr (by omega)
  have hG2 : Complex.Gamma ((t : ℂ) + 1 + 1) = ((t : ℂ) + 1) * Complex.Gamma ((t : ℂ) + 1) :=
    Complex.Gamma_add_one _ ht1ne
  have gN : Complex.Gamma ((t : ℂ) + 1 + (u : ℂ) + s) ≠ 0 := by
    have heq : ((t : ℂ) + 1 + (u : ℂ) + s) = s + ((((t + u : ℕ)) : ℂ) + 1) := by
      push_cast; ring
    rw [heq]
    exact gamma_ne_zero_of_hs s hs (t + u)
  have gt : Complex.Gamma ((t : ℂ) + 1) ≠ 0 := nat_gamma_ne_zero t
  have gt1 : Complex.Gamma ((t : ℂ) + 1 + 1) ≠ 0 := by
    have heq : ((t : ℂ) + 1 + 1) = ((((t + 1 : ℕ)) : ℂ) + 1) := by push_cast; ring
    rw [heq]
    exact nat_gamma_ne_zero (t + 1)
  have gu : Complex.Gamma (s + ((u : ℂ) + 1)) ≠ 0 := gamma_ne_zero_of_hs s hs u
  rw [hG1, hG2]
  field_simp

/-- Pascal identity: C1(m+1) = C2(m+1) + C2(m). -/
private lemma pascal_lemma (s : ℂ) (m w : ℕ)
    (hs : ∀ m : ℕ, s ≠ -((m + 1 : ℕ) : ℂ)) (hs0 : s ≠ 0) :
    Complex.Gamma (((((m + 1 + w : ℕ)) : ℂ) + s) + 1) /
        (Complex.Gamma ((((m + 1 : ℕ)) : ℂ) + 1) *
          Complex.Gamma (((((m + 1 + w : ℕ)) : ℂ) + s) - ((((m + 1 : ℕ)) : ℂ)) + 1))
      = Complex.Gamma ((((m + 1 + w : ℕ)) : ℂ) + s) /
          (Complex.Gamma ((((m + 1 : ℕ)) : ℂ) + 1) *
            Complex.Gamma (((((m + 1 + w : ℕ)) : ℂ) + s) - ((((m + 1 : ℕ)) : ℂ)))) +
        Complex.Gamma ((((m + 1 + w : ℕ)) : ℂ) + s) /
          (Complex.Gamma (((m : ℂ)) + 1) *
            Complex.Gamma (((((m + 1 + w : ℕ)) : ℂ) + s) - (((m : ℂ))))) := by
  have hm1 : ((((m + 1 : ℕ)) : ℂ)) = (m : ℂ) + 1 := by push_cast; ring
  have hcastN : ((((m + 1 + w : ℕ)) : ℂ)) = (m : ℂ) + 1 + (w : ℂ) := by push_cast; ring
  rw [hcastN, hm1]
  have hNa : (((m : ℂ) + 1 + (w : ℂ) + s) - ((m : ℂ) + 1)) ≠ 0 := by
    have heq : (((m : ℂ) + 1 + (w : ℂ) + s) - ((m : ℂ) + 1)) = s + (w : ℂ) := by ring
    rw [heq]
    intro hc
    rcases Nat.eq_zero_or_pos w with rfl | hw
    · simp at hc
      exact hs0 hc
    · obtain ⟨v, rfl⟩ : ∃ v, w = v + 1 := ⟨w - 1, by omega⟩
      apply hs v
      have hsc : s = -((((v + 1 : ℕ))) : ℂ) := by linear_combination hc
      exact hsc
  have hNne : ((m : ℂ) + 1 + (w : ℂ) + s) ≠ 0 := by
    intro hc
    apply hs (m + w)
    have hcast : (((m + w + 1 : ℕ)) : ℂ) = (m : ℂ) + 1 + (w : ℂ) := by push_cast; ring
    have hsc : s = -((((m + w + 1 : ℕ))) : ℂ) := by
      rw [hcast]
      linear_combination hc
    exact hsc
  have hane : ((m : ℂ) + 1) ≠ 0 := by
    have heq : ((m : ℂ) + 1) = ((((m + 1 : ℕ))) : ℂ) := by push_cast; ring
    rw [heq]
    exact Nat.cast_ne_zero.mpr (by omega)
  have hG1 : Complex.Gamma (((m : ℂ) + 1 + (w : ℂ) + s) + 1)
      = ((m : ℂ) + 1 + (w : ℂ) + s) * Complex.Gamma ((m : ℂ) + 1 + (w : ℂ) + s) :=
    Complex.Gamma_add_one _ hNne
  have hG2 : Complex.Gamma (((m : ℂ) + 1) + 1) = ((m : ℂ) + 1) * Complex.Gamma ((m : ℂ) + 1) :=
    Complex.Gamma_add_one _ hane
  have hG3 : Complex.Gamma (((m : ℂ) + 1 + (w : ℂ) + s) - (m : ℂ))
      = (((m : ℂ) + 1 + (w : ℂ) + s) - ((m : ℂ) + 1)) *
        Complex.Gamma (((m : ℂ) + 1 + (w : ℂ) + s) - ((m : ℂ) + 1)) := by
    have heq : (((m : ℂ) + 1 + (w : ℂ) + s) - (m : ℂ))
        = ((((m : ℂ) + 1 + (w : ℂ) + s) - ((m : ℂ) + 1))) + 1 := by ring
    rw [heq]
    exact Complex.Gamma_add_one _ hNa
  have hG4 : Complex.Gamma ((((m : ℂ) + 1 + (w : ℂ) + s) - ((m : ℂ) + 1)) + 1)
      = (((m : ℂ) + 1 + (w : ℂ) + s) - ((m : ℂ) + 1)) *
        Complex.Gamma (((m : ℂ) + 1 + (w : ℂ) + s) - ((m : ℂ) + 1)) :=
    Complex.Gamma_add_one _ hNa
  have gN : Complex.Gamma ((m : ℂ) + 1 + (w : ℂ) + s) ≠ 0 := by
    have heq : ((m : ℂ) + 1 + (w : ℂ) + s) = s + ((((m + 1 + w : ℕ)) : ℂ)) := by
      push_cast; ring
    rw [heq]
    exact gamma_add_nat_ne_zero s (m + 1 + w) hs hs0
  have ga : Complex.Gamma ((m : ℂ) + 1) ≠ 0 := nat_gamma_ne_zero m
  have gNa : Complex.Gamma (((m : ℂ) + 1 + (w : ℂ) + s) - ((m : ℂ) + 1)) ≠ 0 := by
    have heq : (((m : ℂ) + 1 + (w : ℂ) + s) - ((m : ℂ) + 1)) = s + (w : ℂ) := by ring
    rw [heq]
    exact gamma_add_nat_ne_zero s w hs hs0
  have gNm : Complex.Gamma (((m : ℂ) + 1 + (w : ℂ) + s) - (m : ℂ)) ≠ 0 := by
    have heq : (((m : ℂ) + 1 + (w : ℂ) + s) - (m : ℂ)) = s + ((w : ℂ) + 1) := by ring
    rw [heq]
    exact gamma_ne_zero_of_hs s hs w
  have gNa1 : Complex.Gamma ((((m : ℂ) + 1 + (w : ℂ) + s) - ((m : ℂ) + 1)) + 1) ≠ 0 := by
    have heq : ((((m : ℂ) + 1 + (w : ℂ) + s) - ((m : ℂ) + 1)) + 1) = s + ((w : ℂ) + 1) := by ring
    rw [heq]
    exact gamma_ne_zero_of_hs s hs w
  rw [hG1, hG2, hG3, hG4]
  field_simp
  ring

end Work

namespace Work2

open Work

/-- Partial alternating sums: `∑_{k=0}^m (-1)^k C1(k) = (-1)^m C2(m)`. -/
private lemma partial_sum (s : ℂ) (n : ℕ)
    (hs : ∀ m : ℕ, s ≠ -((m + 1 : ℕ) : ℂ)) (hs0 : s ≠ 0) (hn : 0 < n) :
    ∀ m, m ≤ n →
    ∑ k ∈ Finset.range (m + 1),
      ((-1 : ℂ) ^ k *
        (Complex.Gamma ((((n : ℂ) + s)) + 1) /
          (Complex.Gamma ((((k : ℕ)) : ℂ) + 1) *
            Complex.Gamma (((((n : ℂ) + s)) - ((((k : ℕ)) : ℂ))) + 1))))
      = (-1 : ℂ) ^ m *
        (Complex.Gamma (((n : ℂ) + s)) /
          (Complex.Gamma ((((m : ℕ)) : ℂ) + 1) *
            Complex.Gamma ((((n : ℂ) + s)) - ((((m : ℕ)) : ℂ))))) := by
  intro m
  induction m with
  | zero =>
    intro _
    have h01 : (0 : ℕ) + 1 = 1 := rfl
    rw [h01, Finset.sum_range_one]
    simp only [pow_zero, one_mul, Nat.cast_zero, sub_zero, zero_add]
    have gN : Complex.Gamma ((n : ℂ) + s) ≠ 0 := gamma_N_ne_zero s n hs hn
    have gN1 : Complex.Gamma (((n : ℂ) + s) + 1) ≠ 0 := by
      have heq : (((n : ℂ) + s) + 1) = s + (((n : ℕ) : ℂ) + 1) := by ring
      rw [heq]
      exact gamma_ne_zero_of_hs s hs n
    rw [Complex.Gamma_one, one_mul, one_mul, div_self gN1, div_self gN]
  | succ k ih =>
    intro hk1
    have hkn : k ≤ n := by omega
    have ihk := ih hkn
    obtain ⟨w, rfl⟩ : ∃ w, n = k + 1 + w := ⟨n - (k + 1), by omega⟩
    rw [Finset.sum_range_succ, ihk]
    have pascal := pascal_lemma s k w hs hs0
    rw [pascal]
    have hpow : ((-1 : ℂ) ^ (k + 1)) = -(-1 : ℂ) ^ k := by
      rw [pow_succ]; ring
    rw [hpow]
    ring

end Work2

namespace Work3

/-- Triangular interchange of finite sums. -/
private lemma interchange (F : ℕ → ℕ → ℂ) (n : ℕ) :
    (∑ k ∈ Finset.Icc 1 n, ∑ j ∈ Finset.Icc 1 k, F k j)
    = ∑ j ∈ Finset.Icc 1 n, ∑ k ∈ Finset.Icc j n, F k j := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1) (fun k => ∑ j ∈ Finset.Icc 1 k, F k j)]
    rw [ih]
    have hinner : ∀ j ∈ Finset.Icc 1 (n + 1), (∑ k ∈ Finset.Icc j (n + 1), F k j)
        = (∑ k ∈ Finset.Icc j n, F k j) + F (n + 1) j := by
      intro j hj
      have hj1 : j ≤ n + 1 := (Finset.mem_Icc.mp hj).2
      exact Finset.sum_Icc_succ_top hj1 (fun k => F k j)
    have hempty : (∑ k ∈ Finset.Icc (n + 1) n, F k (n + 1)) = 0 := by
      rw [Finset.Icc_eq_empty (by omega : ¬ n + 1 ≤ n)]
      exact Finset.sum_empty
    have hsplit : (∑ j ∈ Finset.Icc 1 (n + 1), ∑ k ∈ Finset.Icc j n, F k j)
        = (∑ j ∈ Finset.Icc 1 n, ∑ k ∈ Finset.Icc j n, F k j) := by
      have h := Finset.sum_Icc_succ_top (show 1 ≤ n + 1 by omega)
        (fun j => ∑ k ∈ Finset.Icc j n, F k j)
      rw [hempty, add_zero] at h
      exact h
    have hRHS : (∑ j ∈ Finset.Icc 1 (n + 1), ∑ k ∈ Finset.Icc j (n + 1), F k j)
        = (∑ j ∈ Finset.Icc 1 n, ∑ k ∈ Finset.Icc j n, F k j)
          + ∑ j ∈ Finset.Icc 1 (n + 1), F (n + 1) j := by
      have hcongr : (∑ j ∈ Finset.Icc 1 (n + 1), ∑ k ∈ Finset.Icc j (n + 1), F k j)
          = ∑ j ∈ Finset.Icc 1 (n + 1),
            ((∑ k ∈ Finset.Icc j n, F k j) + F (n + 1) j) :=
        Finset.sum_congr rfl (fun j hj => hinner j hj)
      rw [hcongr, Finset.sum_add_distrib, hsplit]
    rw [hRHS]

/-- Harmonic numbers as complex sums. -/
private lemma hHlemma (k : ℕ) :
    ((((harmonic k : ℚ))) : ℂ) = ∑ j ∈ Finset.Icc 1 k, (((((j : ℕ))) : ℂ))⁻¹ := by
  rw [harmonic_eq_sum_Icc, Rat.cast_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [Rat.cast_inv, Rat.cast_natCast]

end Work3

namespace Work4

open Work Work2

/-- The `k = 0` binomial term equals 1. -/
private lemma hB0lemma (s : ℂ) (n : ℕ)
    (hs : ∀ m : ℕ, s ≠ -((m + 1 : ℕ) : ℂ)) :
    Complex.Gamma ((((n : ℂ) + s)) + 1) /
        (Complex.Gamma ((((0 : ℕ)) : ℂ) + 1) *
          Complex.Gamma (((((n : ℂ) + s)) - ((((0 : ℕ)) : ℂ))) + 1)) = 1 := by
  simp only [Nat.cast_zero, sub_zero]
  have gN1 : Complex.Gamma (((n : ℂ) + s) + 1) ≠ 0 := by
    have heq : (((n : ℂ) + s) + 1) = s + (((n : ℕ) : ℂ) + 1) := by ring
    rw [heq]
    exact gamma_ne_zero_of_hs s hs n
  rw [zero_add, Complex.Gamma_one, one_mul]
  exact div_self gN1

/-- Inner binomial sums over `Icc (u+1) n`. -/
private lemma inner_sum (s : ℂ) (n : ℕ)
    (hs : ∀ m : ℕ, s ≠ -((m + 1 : ℕ) : ℂ)) (hs0 : s ≠ 0) (hn : 0 < n)
    (u : ℕ) (hu : u + 1 ≤ n) :
    ∑ k ∈ Finset.Icc (u + 1) n,
      ((-1 : ℂ) ^ k *
        (Complex.Gamma ((((n : ℂ) + s)) + 1) /
          (Complex.Gamma ((((k : ℕ)) : ℂ) + 1) *
            Complex.Gamma (((((n : ℂ) + s)) - ((((k : ℕ)) : ℂ))) + 1))))
      = (-1 : ℂ) ^ n *
        (Complex.Gamma (((n : ℂ) + s)) /
          (Complex.Gamma ((((n : ℕ)) : ℂ) + 1) *
            Complex.Gamma (((((n : ℂ) + s)) - ((((n : ℕ)) : ℂ)))))) +
        (-1 : ℂ) ^ (u + 1) *
        (Complex.Gamma (((n : ℂ) + s)) /
          (Complex.Gamma ((((u : ℕ)) : ℂ) + 1) *
            Complex.Gamma (((((n : ℂ) + s)) - ((((u : ℕ)) : ℂ)))))) := by
  have hP := partial_sum s n hs hs0 hn
  have hIco : Finset.Icc (u + 1) n = Finset.Ico (u + 1) (n + 1) := by
    rw [Finset.Ico_add_one_right_eq_Icc]
  rw [hIco, Finset.sum_Ico_eq_sub _ (by omega : u + 1 ≤ n + 1)]
  rw [hP n (by omega), hP u (by omega)]
  have hpow : ((-1 : ℂ) ^ (u + 1)) = -(-1 : ℂ) ^ u := by
    rw [pow_succ]; ring
  rw [hpow]
  ring

/-- The full alternating-row sum minus the `j = 0` term. -/
private lemma second_sum (s : ℂ) (n : ℕ)
    (hs : ∀ m : ℕ, s ≠ -((m + 1 : ℕ) : ℂ)) (hs0 : s ≠ 0) (hn : 0 < n) :
    ∑ j ∈ Finset.Icc 1 n,
      ((-1 : ℂ) ^ j *
        (Complex.Gamma ((((n : ℂ) + s)) + 1) /
          (Complex.Gamma ((((j : ℕ)) : ℂ) + 1) *
            Complex.Gamma (((((n : ℂ) + s)) - ((((j : ℕ)) : ℂ))) + 1))))
      = (-1 : ℂ) ^ n *
        (Complex.Gamma (((n : ℂ) + s)) /
          (Complex.Gamma ((((n : ℕ)) : ℂ) + 1) *
            Complex.Gamma (((((n : ℂ) + s)) - ((((n : ℕ)) : ℂ)))))) - 1 := by
  have hP := partial_sum s n hs hs0 hn
  have hB0 := hB0lemma s n hs
  have hIco : Finset.Icc 1 n = Finset.Ico 1 (n + 1) := by
    rw [Finset.Ico_add_one_right_eq_Icc]
  rw [hIco, Finset.sum_Ico_eq_sub _ (by omega : 1 ≤ n + 1)]
  rw [hP n (by omega), Finset.sum_range_one]
  rw [hB0, pow_zero, mul_one]

end Work4

namespace Work5

open Work Work2 Work3 Work4

/-- Main theorem for `s ≠ 0` (statement matches the wanted theorem exactly). -/
private lemma main_ne (s : ℂ) (n : ℕ)
    (hs : ∀ m : ℕ, s ≠ -((m + 1 : ℕ) : ℂ)) (hs0 : s ≠ 0) (hn : 0 < n) :
    ∑ k ∈ Finset.Icc 1 n,
      ((-1 : ℂ) ^ k *
        (Complex.Gamma (((n : ℂ) + s) + 1) /
          (Complex.Gamma ((k : ℂ) + 1) * Complex.Gamma (((n : ℂ) + s) - (k : ℂ) + 1))) *
        ((harmonic k : ℚ) : ℂ)) =
      (-1 : ℂ) ^ n *
          (Complex.Gamma ((s + (n : ℂ) - 1) + 1) /
            (Complex.Gamma ((n : ℂ) + 1) *
              Complex.Gamma ((s + (n : ℂ) - 1) - (n : ℂ) + 1))) *
          ((harmonic n : ℚ) : ℂ) +
        ((-1 : ℂ) ^ n / (s + (n : ℂ))) *
          (Complex.Gamma ((s + (n : ℂ) - 1) + 1) /
            (Complex.Gamma ((n : ℂ) + 1) *
              Complex.Gamma ((s + (n : ℂ) - 1) - (n : ℂ) + 1))) -
        1 / (s + (n : ℂ)) := by
  have hD1 : (((s + (n : ℂ) - 1)) + 1) = (((n : ℂ) + s)) := by ring
  have hD3 : (((s + (n : ℂ) - 1)) - ((n : ℂ)) + 1) = ((((n : ℂ) + s)) - (((n : ℂ)))) := by
    ring
  have hNsn : (s + (n : ℂ)) = (((n : ℂ) + s)) := by ring
  rw [hD1, hD3, hNsn]
  have hN : (((n : ℂ) + s)) ≠ 0 := by
    rw [← hNsn]
    exact add_ne_zero_of_hs s n hs hn
  have e1 : (∑ k ∈ Finset.Icc 1 n,
        ((-1 : ℂ) ^ k *
          (Complex.Gamma ((((n : ℂ) + s)) + 1) /
            (Complex.Gamma ((((k : ℕ)) : ℂ) + 1) *
              Complex.Gamma (((((n : ℂ) + s)) - ((((k : ℕ)) : ℂ))) + 1))) *
          ((((harmonic k : ℚ))) : ℂ)))
      = ∑ k ∈ Finset.Icc 1 n, ∑ j ∈ Finset.Icc 1 k,
        (((-1 : ℂ) ^ k *
          (Complex.Gamma ((((n : ℂ) + s)) + 1) /
            (Complex.Gamma ((((k : ℕ)) : ℂ) + 1) *
              Complex.Gamma (((((n : ℂ) + s)) - ((((k : ℕ)) : ℂ))) + 1)))) *
          (((((j : ℕ))) : ℂ))⁻¹) :=
    Finset.sum_congr rfl (fun k _ => by rw [hHlemma k, Finset.mul_sum])
  rw [e1, interchange]
  have e2 : (∑ j ∈ Finset.Icc 1 n, ∑ k ∈ Finset.Icc j n,
        (((-1 : ℂ) ^ k *
          (Complex.Gamma ((((n : ℂ) + s)) + 1) /
            (Complex.Gamma ((((k : ℕ)) : ℂ) + 1) *
              Complex.Gamma (((((n : ℂ) + s)) - ((((k : ℕ)) : ℂ))) + 1)))) *
          (((((j : ℕ))) : ℂ))⁻¹))
      = ∑ j ∈ Finset.Icc 1 n,
        ((∑ k ∈ Finset.Icc j n,
          ((-1 : ℂ) ^ k *
            (Complex.Gamma ((((n : ℂ) + s)) + 1) /
              (Complex.Gamma ((((k : ℕ)) : ℂ) + 1) *
                Complex.Gamma (((((n : ℂ) + s)) - ((((k : ℕ)) : ℂ))) + 1))))) *
          (((((j : ℕ))) : ℂ))⁻¹) :=
    Finset.sum_congr rfl (fun j _ => (Finset.sum_mul _ _ _).symm)
  rw [e2]
  have e3 : ∀ j ∈ Finset.Icc 1 n,
      (∑ k ∈ Finset.Icc j n,
        ((-1 : ℂ) ^ k *
          (Complex.Gamma ((((n : ℂ) + s)) + 1) /
            (Complex.Gamma ((((k : ℕ)) : ℂ) + 1) *
              Complex.Gamma (((((n : ℂ) + s)) - ((((k : ℕ)) : ℂ))) + 1)))))
      = (-1 : ℂ) ^ n *
        (Complex.Gamma (((n : ℂ) + s)) /
          (Complex.Gamma ((((n : ℕ)) : ℂ) + 1) *
            Complex.Gamma (((((n : ℂ) + s)) - ((((n : ℕ)) : ℂ)))))) +
        (-1 : ℂ) ^ j *
        (Complex.Gamma (((n : ℂ) + s)) /
          (Complex.Gamma ((((j - 1 : ℕ)) : ℂ) + 1) *
            Complex.Gamma (((((n : ℂ) + s)) - ((((j - 1 : ℕ)) : ℂ)))))) := by
    intro j hj
    have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
    have hjn : j ≤ n := (Finset.mem_Icc.mp hj).2
    obtain ⟨u, rfl⟩ : ∃ u, j = u + 1 := ⟨j - 1, by omega⟩
    have h := inner_sum s n hs hs0 hn u (by omega)
    rw [Nat.add_sub_cancel]
    exact h
  have e5 : (∑ j ∈ Finset.Icc 1 n,
        ((∑ k ∈ Finset.Icc j n,
          ((-1 : ℂ) ^ k *
            (Complex.Gamma ((((n : ℂ) + s)) + 1) /
              (Complex.Gamma ((((k : ℕ)) : ℂ) + 1) *
                Complex.Gamma (((((n : ℂ) + s)) - ((((k : ℕ)) : ℂ))) + 1))))) *
          (((((j : ℕ))) : ℂ))⁻¹))
      = ∑ j ∈ Finset.Icc 1 n,
        (((-1 : ℂ) ^ n *
          (Complex.Gamma (((n : ℂ) + s)) /
            (Complex.Gamma ((((n : ℕ)) : ℂ) + 1) *
              Complex.Gamma (((((n : ℂ) + s)) - ((((n : ℕ)) : ℂ)))))) +
          (-1 : ℂ) ^ j *
          (Complex.Gamma (((n : ℂ) + s)) /
            (Complex.Gamma ((((j - 1 : ℕ)) : ℂ) + 1) *
              Complex.Gamma (((((n : ℂ) + s)) - ((((j - 1 : ℕ)) : ℂ))))))) *
          (((((j : ℕ))) : ℂ))⁻¹) :=
    Finset.sum_congr rfl (fun j hj => by rw [e3 j hj])
  rw [e5]
  have erat : ∀ j ∈ Finset.Icc 1 n,
      (((-1 : ℂ) ^ j *
        (Complex.Gamma (((n : ℂ) + s)) /
          (Complex.Gamma ((((j - 1 : ℕ)) : ℂ) + 1) *
            Complex.Gamma (((((n : ℂ) + s)) - ((((j - 1 : ℕ)) : ℂ))))))) *
        (((((j : ℕ))) : ℂ))⁻¹)
      = ((((n : ℂ) + s)))⁻¹ *
        ((-1 : ℂ) ^ j *
          (Complex.Gamma ((((n : ℂ) + s)) + 1) /
            (Complex.Gamma ((((j : ℕ)) : ℂ) + 1) *
              Complex.Gamma (((((n : ℂ) + s)) - ((((j : ℕ)) : ℂ))) + 1)))) := by
    intro j hj
    have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
    have hjn : j ≤ n := (Finset.mem_Icc.mp hj).2
    obtain ⟨u, rfl⟩ : ∃ u, j = u + 1 := ⟨j - 1, by omega⟩
    have hr := ratio_lemma s n u (n - (u + 1)) (by omega : n = u + 1 + (n - (u + 1))) hs
    have hcast : ((((u + 1 : ℕ))) : ℂ) = ((((u : ℕ)) : ℂ) + 1) := by push_cast; ring
    rw [Nat.add_sub_cancel]
    rw [hcast] at hr ⊢
    have h2 := hr
    simp only [div_eq_mul_inv] at h2
    linear_combination ((-1 : ℂ) ^ (u + 1)) * h2
  have e6 : (∑ j ∈ Finset.Icc 1 n,
        (((-1 : ℂ) ^ n *
          (Complex.Gamma (((n : ℂ) + s)) /
            (Complex.Gamma ((((n : ℕ)) : ℂ) + 1) *
              Complex.Gamma (((((n : ℂ) + s)) - ((((n : ℕ)) : ℂ)))))) +
          (-1 : ℂ) ^ j *
          (Complex.Gamma (((n : ℂ) + s)) /
            (Complex.Gamma ((((j - 1 : ℕ)) : ℂ) + 1) *
              Complex.Gamma (((((n : ℂ) + s)) - ((((j - 1 : ℕ)) : ℂ))))))) *
          (((((j : ℕ))) : ℂ))⁻¹))
      = (-1 : ℂ) ^ n *
        (Complex.Gamma (((n : ℂ) + s)) /
          (Complex.Gamma ((((n : ℕ)) : ℂ) + 1) *
            Complex.Gamma (((((n : ℂ) + s)) - ((((n : ℕ)) : ℂ)))))) *
        (∑ j ∈ Finset.Icc 1 n, (((((j : ℕ))) : ℂ))⁻¹) +
        ((((n : ℂ) + s)))⁻¹ *
        (∑ j ∈ Finset.Icc 1 n,
          ((-1 : ℂ) ^ j *
            (Complex.Gamma ((((n : ℂ) + s)) + 1) /
              (Complex.Gamma ((((j : ℕ)) : ℂ) + 1) *
                Complex.Gamma (((((n : ℂ) + s)) - ((((j : ℕ)) : ℂ))) + 1))))) := by
    have e6a : ∀ j ∈ Finset.Icc 1 n,
        (((-1 : ℂ) ^ n *
          (Complex.Gamma (((n : ℂ) + s)) /
            (Complex.Gamma ((((n : ℕ)) : ℂ) + 1) *
              Complex.Gamma (((((n : ℂ) + s)) - ((((n : ℕ)) : ℂ)))))) +
          (-1 : ℂ) ^ j *
          (Complex.Gamma (((n : ℂ) + s)) /
            (Complex.Gamma ((((j - 1 : ℕ)) : ℂ) + 1) *
              Complex.Gamma (((((n : ℂ) + s)) - ((((j - 1 : ℕ)) : ℂ))))))) *
          (((((j : ℕ))) : ℂ))⁻¹)
        = ((-1 : ℂ) ^ n *
          (Complex.Gamma (((n : ℂ) + s)) /
            (Complex.Gamma ((((n : ℕ)) : ℂ) + 1) *
              Complex.Gamma (((((n : ℂ) + s)) - ((((n : ℕ)) : ℂ)))))) *
          (((((j : ℕ))) : ℂ))⁻¹) +
          (((((n : ℂ) + s)))⁻¹ *
          ((-1 : ℂ) ^ j *
            (Complex.Gamma ((((n : ℂ) + s)) + 1) /
              (Complex.Gamma ((((j : ℕ)) : ℂ) + 1) *
                Complex.Gamma (((((n : ℂ) + s)) - ((((j : ℕ)) : ℂ))) + 1))))) := by
      intro j hj
      rw [add_mul, erat j hj]
    rw [Finset.sum_congr rfl (fun j hj => e6a j hj), Finset.sum_add_distrib,
      (Finset.mul_sum _ _ _).symm, (Finset.mul_sum _ _ _).symm]
  rw [e6, ← hHlemma n, second_sum s n hs hs0 hn]
  ring

end Work5

namespace Work6

open Work3

/-- At `s = 0`, the Gamma quotient is an ordinary binomial coefficient. -/
private lemma chooseB_eq (n k : ℕ) (hkn : k ≤ n) :
    Complex.Gamma ((((n : ℂ) + (0 : ℂ))) + 1) /
      (Complex.Gamma ((((k : ℕ)) : ℂ) + 1) *
        Complex.Gamma (((((n : ℂ) + (0 : ℂ))) - ((((k : ℕ)) : ℂ))) + 1))
    = ((n.choose k : ℕ) : ℂ) := by
  have e1 : ((((n : ℂ) + (0 : ℂ))) + 1) = ((((n : ℕ)) : ℂ) + 1) := by ring
  have e2 : (((((n : ℂ) + (0 : ℂ))) - ((((k : ℕ)) : ℂ))) + 1) = ((((n - k : ℕ)) : ℂ) + 1) := by
    rw [add_zero, ← Nat.cast_sub hkn]
  rw [e1, e2, Complex.Gamma_nat_eq_factorial, Complex.Gamma_nat_eq_factorial,
    Complex.Gamma_nat_eq_factorial]
  have h := Nat.choose_mul_factorial_mul_factorial hkn
  have hC : ((n.choose k : ℕ) : ℂ) * ((k.factorial : ℕ) : ℂ) * ((((n - k).factorial : ℕ)) : ℂ)
      = ((n.factorial : ℕ) : ℂ) := by
    exact_mod_cast h
  have hk : ((k.factorial : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hnk : ((((n - k).factorial : ℕ)) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hden : ((k.factorial : ℕ) : ℂ) * ((((n - k).factorial : ℕ)) : ℂ) ≠ 0 :=
    mul_ne_zero hk hnk
  rw [div_eq_iff hden]
  linear_combination hC.symm

/-- At `s = 0`, the `D` quotient vanishes. -/
private lemma chooseD_zero (n : ℕ) :
    Complex.Gamma ((((0 : ℂ) + (n : ℂ) - 1)) + 1) /
      (Complex.Gamma ((((n : ℕ)) : ℂ) + 1) *
        Complex.Gamma (((((0 : ℂ) + (n : ℂ) - 1)) - ((((n : ℕ)) : ℂ))) + 1)) = 0 := by
  have e0 : (((((0 : ℂ) + (n : ℂ) - 1)) - ((((n : ℕ)) : ℂ))) + 1) = 0 := by ring
  rw [e0, Complex.Gamma_zero, mul_zero, div_zero]

/-- Partial alternating ordinary-binomial sums. -/
private lemma partial_sum_zero (N m : ℕ) :
    ∑ k ∈ Finset.range (m + 1), ((-1 : ℂ) ^ k * ((N + 1).choose k : ℂ))
    = (-1 : ℂ) ^ m * (N.choose m : ℂ) := by
  have h := Int.alternating_sum_range_choose_eq_choose (n := N) (m := m)
  have step1 : (∑ k ∈ Finset.range (m + 1), ((-1 : ℂ) ^ k * ((N + 1).choose k : ℂ)))
      = Int.cast (∑ k ∈ Finset.range (m + 1), (-1 : ℤ) ^ k * ((N + 1).choose k : ℤ)) := by
    rw [Int.cast_sum]
    apply Finset.sum_congr rfl
    intro k _
    push_cast
    ring
  rw [h] at step1
  have hcc2 : Int.cast ((-1 : ℤ) ^ m * (N.choose m : ℤ))
      = (-1 : ℂ) ^ m * (N.choose m : ℂ) := by
    push_cast
    ring
  rw [hcc2] at step1
  exact step1

/-- Full alternating ordinary-binomial sums vanish. -/
private lemma full_zero (n : ℕ) (hn : 0 < n) :
    ∑ k ∈ Finset.range (n + 1), ((-1 : ℂ) ^ k * (n.choose k : ℂ)) = 0 := by
  have h := Int.alternating_sum_range_choose_of_ne (show n ≠ 0 by omega)
  have step1 : (∑ k ∈ Finset.range (n + 1), ((-1 : ℂ) ^ k * (n.choose k : ℂ)))
      = Int.cast (∑ k ∈ Finset.range (n + 1), (-1 : ℤ) ^ k * (n.choose k : ℤ)) := by
    rw [Int.cast_sum]
    apply Finset.sum_congr rfl
    intro k _
    push_cast
    ring
  rw [h] at step1
  rw [Int.cast_zero] at step1
  exact step1

/-- Ratio identity for ordinary binomial coefficients. -/
private lemma ratio_zero (N u : ℕ) :
    ((N.choose u : ℕ) : ℂ) / ((((u : ℕ)) : ℂ) + 1)
    = ((((N + 1).choose (u + 1) : ℕ)) : ℂ) / ((((N : ℕ)) : ℂ) + 1) := by
  have h := Nat.add_one_mul_choose_eq N u
  have h2 : ((((N + 1 : ℕ))) : ℂ) * ((N.choose u : ℂ))
      = ((((N + 1).choose (u + 1) : ℕ)) : ℂ) * ((((u + 1 : ℕ))) : ℂ) := by
    exact_mod_cast h
  have eN : ((((N + 1 : ℕ))) : ℂ) = ((((N : ℕ)) : ℂ) + 1) := Nat.cast_add_one N
  have eu : ((((u + 1 : ℕ))) : ℂ) = ((((u : ℕ)) : ℂ) + 1) := Nat.cast_add_one u
  rw [eN, eu] at h2
  have hju : ((((u : ℕ)) : ℂ) + 1) ≠ 0 := by
    have heq : ((((u : ℕ)) : ℂ) + 1) = ((((u + 1 : ℕ))) : ℂ) := (Nat.cast_add_one u).symm
    rw [heq]
    exact Nat.cast_ne_zero.mpr (by omega)
  have hNu : ((((N : ℕ)) : ℂ) + 1) ≠ 0 := by
    have heq : ((((N : ℕ)) : ℂ) + 1) = ((((N + 1 : ℕ))) : ℂ) := (Nat.cast_add_one N).symm
    rw [heq]
    exact Nat.cast_ne_zero.mpr (by omega)
  rw [div_eq_div_iff hju hNu]
  linear_combination h2

/-- Inner sums at `s = 0`. -/
private lemma inner_sum_zero (N u : ℕ) (hu : u + 1 ≤ N + 1) :
    ∑ k ∈ Finset.Icc (u + 1) (N + 1), ((-1 : ℂ) ^ k * (((N + 1).choose k : ℕ) : ℂ))
    = (-1 : ℂ) ^ (u + 1) * ((N.choose u : ℂ)) := by
  have hIco : Finset.Icc (u + 1) (N + 1) = Finset.Ico (u + 1) (N + 1 + 1) :=
    (Finset.Ico_add_one_right_eq_Icc _ _).symm
  rw [hIco, Finset.sum_Ico_eq_sub _ (by omega : u + 1 ≤ N + 1 + 1)]
  rw [full_zero (N + 1) (by omega), partial_sum_zero N u]
  have hpow : ((-1 : ℂ) ^ (u + 1)) = -(-1 : ℂ) ^ u := by
    rw [pow_succ]; ring
  rw [hpow]
  ring

/-- The outer alternating sum at `s = 0`. -/
private lemma second_sum_zero (N : ℕ) :
    ∑ j ∈ Finset.Icc 1 (N + 1), ((-1 : ℂ) ^ j * (((N + 1).choose j : ℕ) : ℂ)) = -1 := by
  have hIco : Finset.Icc 1 (N + 1) = Finset.Ico 1 (N + 1 + 1) :=
    (Finset.Ico_add_one_right_eq_Icc _ _).symm
  rw [hIco, Finset.sum_Ico_eq_sub _ (by omega : 1 ≤ N + 1 + 1)]
  rw [full_zero (N + 1) (by omega), Finset.sum_range_one]
  simp [Nat.choose_zero_right]

end Work6

namespace Work7

open Work3 Work4 Work6

/-- Main theorem for `s = 0` (statement is the wanted theorem with `s := 0`). -/
private lemma main_zero (n : ℕ) (hn : 0 < n) :
    ∑ k ∈ Finset.Icc 1 n,
      ((-1 : ℂ) ^ k *
        (Complex.Gamma (((n : ℂ) + 0) + 1) /
          (Complex.Gamma ((k : ℂ) + 1) * Complex.Gamma (((n : ℂ) + 0) - (k : ℂ) + 1))) *
        ((harmonic k : ℚ) : ℂ)) =
      (-1 : ℂ) ^ n *
          (Complex.Gamma ((0 + (n : ℂ) - 1) + 1) /
            (Complex.Gamma ((n : ℂ) + 1) *
              Complex.Gamma ((0 + (n : ℂ) - 1) - (n : ℂ) + 1))) *
          ((harmonic n : ℚ) : ℂ) +
        ((-1 : ℂ) ^ n / (0 + (n : ℂ))) *
          (Complex.Gamma ((0 + (n : ℂ) - 1) + 1) /
            (Complex.Gamma ((n : ℂ) + 1) *
              Complex.Gamma ((0 + (n : ℂ) - 1) - (n : ℂ) + 1))) -
        1 / (0 + (n : ℂ)) := by
  obtain ⟨N, rfl⟩ : ∃ N, n = N + 1 := ⟨n - 1, by omega⟩
  have eB : ∀ k ∈ Finset.Icc 1 (N + 1),
      ((-1 : ℂ) ^ k *
        (Complex.Gamma ((((N + 1 : ℕ) : ℂ) + (0 : ℂ)) + 1) /
          (Complex.Gamma ((((k : ℕ)) : ℂ) + 1) *
            Complex.Gamma (((((N + 1 : ℕ) : ℂ) + (0 : ℂ))) - ((((k : ℕ)) : ℂ)) + 1))) *
        ((((harmonic k : ℚ))) : ℂ))
      = (((-1 : ℂ) ^ k * ((((N + 1).choose k : ℕ)) : ℂ)) * ((((harmonic k : ℚ))) : ℂ)) := by
    intro k hk
    have hkn : k ≤ N + 1 := (Finset.mem_Icc.mp hk).2
    rw [chooseB_eq (N + 1) k hkn]
  rw [Finset.sum_congr rfl (fun k hk => eB k hk)]
  have e1z : (∑ k ∈ Finset.Icc 1 (N + 1),
        (((-1 : ℂ) ^ k * ((((N + 1).choose k : ℕ)) : ℂ)) * ((((harmonic k : ℚ))) : ℂ)))
      = ∑ k ∈ Finset.Icc 1 (N + 1), ∑ j ∈ Finset.Icc 1 k,
        (((-1 : ℂ) ^ k * ((((N + 1).choose k : ℕ)) : ℂ)) * (((((j : ℕ))) : ℂ))⁻¹) :=
    Finset.sum_congr rfl (fun k _ => by rw [hHlemma k, Finset.mul_sum])
  rw [e1z, interchange]
  have e2z : (∑ j ∈ Finset.Icc 1 (N + 1), ∑ k ∈ Finset.Icc j (N + 1),
        (((-1 : ℂ) ^ k * ((((N + 1).choose k : ℕ)) : ℂ)) * (((((j : ℕ))) : ℂ))⁻¹))
      = ∑ j ∈ Finset.Icc 1 (N + 1),
        ((∑ k ∈ Finset.Icc j (N + 1), ((-1 : ℂ) ^ k * ((((N + 1).choose k : ℕ)) : ℂ))) *
          (((((j : ℕ))) : ℂ))⁻¹) :=
    Finset.sum_congr rfl (fun j _ => (Finset.sum_mul _ _ _).symm)
  rw [e2z]
  have e3z : ∀ j ∈ Finset.Icc 1 (N + 1),
      (∑ k ∈ Finset.Icc j (N + 1), ((-1 : ℂ) ^ k * ((((N + 1).choose k : ℕ)) : ℂ)))
      = (-1 : ℂ) ^ j * (((N.choose (j - 1) : ℕ)) : ℂ) := by
    intro j hj
    have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
    have hjn : j ≤ N + 1 := (Finset.mem_Icc.mp hj).2
    obtain ⟨u, rfl⟩ : ∃ u, j = u + 1 := ⟨j - 1, by omega⟩
    have h := inner_sum_zero N u (by omega)
    rw [Nat.add_sub_cancel]
    exact h
  have e5z : (∑ j ∈ Finset.Icc 1 (N + 1),
        ((∑ k ∈ Finset.Icc j (N + 1), ((-1 : ℂ) ^ k * ((((N + 1).choose k : ℕ)) : ℂ))) *
          (((((j : ℕ))) : ℂ))⁻¹))
      = ∑ j ∈ Finset.Icc 1 (N + 1),
        (((-1 : ℂ) ^ j * (((N.choose (j - 1) : ℕ)) : ℂ)) * (((((j : ℕ))) : ℂ))⁻¹) :=
    Finset.sum_congr rfl (fun j hj => by rw [e3z j hj])
  rw [e5z]
  have eratz : ∀ j ∈ Finset.Icc 1 (N + 1),
      (((-1 : ℂ) ^ j * (((N.choose (j - 1) : ℕ)) : ℂ)) * (((((j : ℕ))) : ℂ))⁻¹)
      = ((((N : ℕ)) : ℂ) + 1)⁻¹ * ((-1 : ℂ) ^ j * ((((N + 1).choose j : ℕ)) : ℂ)) := by
    intro j hj
    have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
    have hjn : j ≤ N + 1 := (Finset.mem_Icc.mp hj).2
    obtain ⟨u, rfl⟩ : ∃ u, j = u + 1 := ⟨j - 1, by omega⟩
    have hr := ratio_zero N u
    rw [Nat.add_sub_cancel]
    have ecast : ((((u + 1 : ℕ))) : ℂ) = ((((u : ℕ)) : ℂ) + 1) := Nat.cast_add_one u
    rw [ecast]
    have h2 := hr
    rw [div_eq_mul_inv, div_eq_mul_inv] at h2
    linear_combination ((-1 : ℂ) ^ (u + 1)) * h2
  have e6z : (∑ j ∈ Finset.Icc 1 (N + 1),
        (((-1 : ℂ) ^ j * (((N.choose (j - 1) : ℕ)) : ℂ)) * (((((j : ℕ))) : ℂ))⁻¹))
      = ((((N : ℕ)) : ℂ) + 1)⁻¹ *
        (∑ j ∈ Finset.Icc 1 (N + 1), ((-1 : ℂ) ^ j * ((((N + 1).choose j : ℕ)) : ℂ))) := by
    have e6a : ∀ j ∈ Finset.Icc 1 (N + 1),
        (((-1 : ℂ) ^ j * (((N.choose (j - 1) : ℕ)) : ℂ)) * (((((j : ℕ))) : ℂ))⁻¹)
        = ((((N : ℕ)) : ℂ) + 1)⁻¹ * ((-1 : ℂ) ^ j * ((((N + 1).choose j : ℕ)) : ℂ)) :=
      fun j hj => eratz j hj
    rw [Finset.sum_congr rfl (fun j hj => e6a j hj), ← Finset.mul_sum]
  rw [e6z, second_sum_zero N]
  have eD := chooseD_zero (N + 1)
  have h0N : (0 : ℂ) + ((((N + 1 : ℕ))) : ℂ) = ((((N + 1 : ℕ))) : ℂ) := by ring
  have ecastN : ((((N + 1 : ℕ))) : ℂ) = ((((N : ℕ)) : ℂ) + 1) := Nat.cast_add_one N
  rw [eD, h0N, ecastN]
  ring

end Work7

@[expose] public section

namespace MetaMathlibExt

/-- **Alternating binomial transform of the harmonic numbers.** Let $s$ be a complex number that
is not a negative integer, let $n$ be a positive integer, and let $H_k = \sum_{j=1}^{k} 1/j$
be the $k$-th harmonic number. For complex $z$ and natural $k$ write
$\binom{z}{k} = \Gamma(z + 1) / (\Gamma(k + 1)\,\Gamma(z - k + 1))$, with $1/\Gamma$ taken to
be $0$ at the poles of $\Gamma$. Then

$$
\sum_{k=1}^{n} (-1)^k \binom{n+s}{k} H_k = (-1)^n \binom{s+n-1}{n} H_n +
\frac{(-1)^n}{s+n} \binom{s+n-1}{n} - \frac{1}{s+n}.
$$

The generalized binomial coefficients are written as Gamma-function quotients, and the
assumption that $s$ is not a negative integer is the source condition
$s \in \mathbb{C} \setminus \mathbb{Z}^-$.

Source: Necdet Batır, "Finite Binomial Sum Identities with Harmonic
Numbers," Journal of Integer Sequences 24 (2021), Article 21.4.3,
Corollary 3 (label Corollary3), lines 220–226,
https://cs.uwaterloo.ca/journals/JIS/VOL24/Batir2/batir13.tex
-/
theorem alternating_binomial_transform_harmonic_numbers (s : ℂ) (n : ℕ)
    (hs : ∀ m : ℕ, s ≠ -((m + 1 : ℕ) : ℂ)) (hn : 0 < n) :
    ∑ k ∈ Finset.Icc 1 n,
      ((-1 : ℂ) ^ k *
        (Complex.Gamma (((n : ℂ) + s) + 1) /
          (Complex.Gamma ((k : ℂ) + 1) * Complex.Gamma (((n : ℂ) + s) - (k : ℂ) + 1))) *
        ((harmonic k : ℚ) : ℂ)) =
      (-1 : ℂ) ^ n *
          (Complex.Gamma ((s + (n : ℂ) - 1) + 1) /
            (Complex.Gamma ((n : ℂ) + 1) *
              Complex.Gamma ((s + (n : ℂ) - 1) - (n : ℂ) + 1))) *
          ((harmonic n : ℚ) : ℂ) +
        ((-1 : ℂ) ^ n / (s + (n : ℂ))) *
          (Complex.Gamma ((s + (n : ℂ) - 1) + 1) /
            (Complex.Gamma ((n : ℂ) + 1) *
              Complex.Gamma ((s + (n : ℂ) - 1) - (n : ℂ) + 1))) -
        1 / (s + (n : ℂ)) := by
  by_cases hs0 : s = 0
  · subst hs0
    exact Work7.main_zero n hn
  · exact Work5.main_ne s n hs hs0 hn

end MetaMathlibExt
