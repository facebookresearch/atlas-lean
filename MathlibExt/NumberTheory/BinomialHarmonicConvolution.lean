/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.Harmonic.Defs
public import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Int.Star
import Mathlib.Data.Rat.Star
import Mathlib.GroupTheory.Finiteness
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Tactic.Positivity.Basic

@[expose] public section

namespace MetaMathlibExt

private lemma sum_harmonic_Icc (m : ℕ) :
    ∑ ν ∈ Finset.Icc 1 m, harmonic ν =
      ((m + 1 : ℕ) : ℚ) * harmonic m - (m : ℚ) := by
  induction m with
  | zero => simp
  | succ n ih =>
    have h1 : (1 : ℕ) ≤ n + 1 := by omega
    rw [Finset.sum_Icc_succ_top h1]
    rw [ih]
    rw [harmonic_succ]
    have hpos : ((n : ℚ) + 1) ≠ 0 := by positivity
    push_cast
    field_simp
    ring

private def Lsum (a b : ℕ) : ℚ :=
  ∑ ν ∈ Finset.Icc 1 (a + 1),
    ((((Nat.choose (a + b + 1 - ν) a : ℕ)) : ℚ) -
     (((Nat.choose (a + b + 1 - ν) b : ℕ)) : ℚ)) * harmonic ν

private def Rval (a b : ℕ) : ℚ :=
  ((Nat.choose (a + b + 2) (b + 1) : ℕ) : ℚ) * (harmonic (b + 1) - harmonic (a + 1))

private lemma absorb_key (A B : ℕ) :
    ((B + 2 : ℕ) : ℚ) * ((Nat.choose (A + B + 3) (B + 2) : ℕ) : ℚ) =
      ((A + 2 : ℕ) : ℚ) * ((Nat.choose (A + B + 3) (B + 1) : ℕ) : ℚ) := by
  have h : Nat.choose (A + B + 3) (B + 2) * (B + 2)
      = Nat.choose (A + B + 3) (B + 1) * (A + 2) := by
    have h1 := Nat.choose_succ_right_eq (A + B + 3) (B + 1)
    have h2 : (A + B + 3) - (B + 1) = A + 2 := by omega
    rw [h2] at h1
    linarith [h1]
  have hQ : ((((Nat.choose (A + B + 3) (B + 2) * (B + 2) : ℕ))) : ℚ)
      = ((((Nat.choose (A + B + 3) (B + 1) * (A + 2) : ℕ))) : ℚ) := by rw [h]
  push_cast at hQ
  push_cast
  linear_combination hQ

private lemma R_add (A B : ℕ) :
    ((Nat.choose (A + B + 3 + 1) (B + 2) : ℕ) : ℚ) *
        (harmonic (B + 2) - harmonic (A + 2)) =
      ((Nat.choose (A + B + 3) (B + 2) : ℕ) : ℚ) *
        (harmonic (B + 2) - harmonic (A + 1)) +
      ((Nat.choose (A + B + 3) (B + 1) : ℕ) : ℚ) *
        (harmonic (B + 1) - harmonic (A + 2)) := by
  have hP : ((Nat.choose (A + B + 3 + 1) (B + 2) : ℕ) : ℚ)
      = ((Nat.choose (A + B + 3) (B + 1) : ℕ) : ℚ)
        + ((Nat.choose (A + B + 3) (B + 2) : ℕ) : ℚ) := by
    have h := Nat.choose_succ_succ (A + B + 3) (B + 1)
    have e : B + 2 = (B + 1) + 1 := by omega
    rw [e] at *
    have h2 : A + B + 3 + 1 = (A + B + 3) + 1 := by omega
    rw [h2]
    exact_mod_cast h
  have hHB : harmonic (B + 2) = harmonic (B + 1) + (((B + 2 : ℕ)) : ℚ)⁻¹ := by
    have h2 : B + 2 = (B + 1) + 1 := by omega
    conv_lhs => rw [h2]
    rw [harmonic_succ]
  have hHA : harmonic (A + 2) = harmonic (A + 1) + (((A + 2 : ℕ)) : ℚ)⁻¹ := by
    have h2 : A + 2 = (A + 1) + 1 := by omega
    conv_lhs => rw [h2]
    rw [harmonic_succ]
  have hBne : (((B + 2 : ℕ)) : ℚ) ≠ 0 := by positivity
  have hAne : (((A + 2 : ℕ)) : ℚ) ≠ 0 := by positivity
  have habs := absorb_key A B
  push_cast at habs
  have key : ((Nat.choose (A + B + 3) (B + 1) : ℕ) : ℚ) * ((((B + 2 : ℕ)) : ℚ))⁻¹
      = ((Nat.choose (A + B + 3) (B + 2) : ℕ) : ℚ) * ((((A + 2 : ℕ)) : ℚ))⁻¹ := by
    rw [← div_eq_mul_inv, ← div_eq_mul_inv]
    rw [div_eq_div_iff hBne hAne]
    have hB2 : (((B + 2 : ℕ)) : ℚ) = ((B : ℚ) + 2) := by push_cast; ring
    have hA2 : (((A + 2 : ℕ)) : ℚ) = ((A : ℚ) + 2) := by push_cast; ring
    rw [← hB2, ← hA2] at habs
    linear_combination -habs
  rw [hP, hHB, hHA]
  linear_combination key

private lemma R_add' (A B : ℕ) :
    Rval (A + 1) (B + 1) = Rval A (B + 1) + Rval (A + 1) B := by
  simp only [Rval]
  have e1 : (A + 1) + (B + 1) + 2 = A + B + 3 + 1 := by omega
  have e2 : (B + 1) + 1 = B + 2 := by omega
  have e3 : A + (B + 1) + 2 = A + B + 3 := by omega
  have e4 : (A + 1) + B + 2 = A + B + 3 := by omega
  have e5 : (A + 1) + 1 = A + 2 := by omega
  rw [e1, e2, e3, e4, e5]
  exact R_add A B

private lemma R_diag (a : ℕ) : Rval a a = 0 := by
  simp [Rval]

private lemma L_diag (a : ℕ) : Lsum a a = 0 := by
  simp only [Lsum]
  apply Finset.sum_eq_zero
  intro ν hν
  rw [sub_self, zero_mul]

private lemma L_add' (A B : ℕ) (hlt : B < A) :
    Lsum (A + 1) (B + 1) = Lsum A (B + 1) + Lsum (A + 1) B := by
  simp only [Lsum]
  have h1 : (1 : ℕ) ≤ A + 1 + 1 := by omega
  rw [Finset.sum_Icc_succ_top h1 _]
  rw [Finset.sum_Icc_succ_top h1 _]
  have hterm : ∀ ν ∈ Finset.Icc 1 (A + 1),
      ((((Nat.choose ((A + 1) + (B + 1) + 1 - ν) (A + 1) : ℕ)) : ℚ) -
       (((Nat.choose ((A + 1) + (B + 1) + 1 - ν) (B + 1) : ℕ)) : ℚ)) * harmonic ν =
      ((((Nat.choose (A + (B + 1) + 1 - ν) A : ℕ)) : ℚ) -
       (((Nat.choose (A + (B + 1) + 1 - ν) (B + 1) : ℕ)) : ℚ)) * harmonic ν +
      ((((Nat.choose ((A + 1) + B + 1 - ν) (A + 1) : ℕ)) : ℚ) -
       (((Nat.choose ((A + 1) + B + 1 - ν) B : ℕ)) : ℚ)) * harmonic ν := by
    intro ν hν
    have hν1 : 1 ≤ ν := (Finset.mem_Icc.mp hν).1
    have hν2 : ν ≤ A + 1 := (Finset.mem_Icc.mp hν).2
    have eD : (A + 1) + (B + 1) + 1 - ν = (A + B + 2 - ν) + 1 := by omega
    have eE : A + (B + 1) + 1 - ν = A + B + 2 - ν := by omega
    have eF : (A + 1) + B + 1 - ν = A + B + 2 - ν := by omega
    rw [eD, eE, eF]
    have pAQ : (((Nat.choose ((A + B + 2 - ν) + 1) (A + 1) : ℕ)) : ℚ)
        = (((Nat.choose (A + B + 2 - ν) A : ℕ)) : ℚ)
          + (((Nat.choose (A + B + 2 - ν) (A + 1) : ℕ)) : ℚ) := by
      exact_mod_cast Nat.choose_succ_succ (A + B + 2 - ν) A
    have pBQ : (((Nat.choose ((A + B + 2 - ν) + 1) (B + 1) : ℕ)) : ℚ)
        = (((Nat.choose (A + B + 2 - ν) B : ℕ)) : ℚ)
          + (((Nat.choose (A + B + 2 - ν) (B + 1) : ℕ)) : ℚ) := by
      exact_mod_cast Nat.choose_succ_succ (A + B + 2 - ν) B
    rw [pAQ, pBQ]
    ring
  have hmid : (∑ ν ∈ Finset.Icc 1 (A + 1),
      ((((Nat.choose ((A + 1) + (B + 1) + 1 - ν) (A + 1) : ℕ)) : ℚ) -
       (((Nat.choose ((A + 1) + (B + 1) + 1 - ν) (B + 1) : ℕ)) : ℚ)) * harmonic ν) =
      (∑ ν ∈ Finset.Icc 1 (A + 1),
      ((((Nat.choose (A + (B + 1) + 1 - ν) A : ℕ)) : ℚ) -
       (((Nat.choose (A + (B + 1) + 1 - ν) (B + 1) : ℕ)) : ℚ)) * harmonic ν) +
      (∑ ν ∈ Finset.Icc 1 (A + 1),
      ((((Nat.choose ((A + 1) + B + 1 - ν) (A + 1) : ℕ)) : ℚ) -
       (((Nat.choose ((A + 1) + B + 1 - ν) B : ℕ)) : ℚ)) * harmonic ν) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl hterm
  have eDl : (A + 1) + (B + 1) + 1 - (A + 1 + 1) = B + 1 := by omega
  have eFl : (A + 1) + B + 1 - (A + 1 + 1) = B := by omega
  have z1 : Nat.choose (B + 1) (A + 1) = 0 := Nat.choose_eq_zero_of_lt (by omega)
  have z2 : Nat.choose B (A + 1) = 0 := Nat.choose_eq_zero_of_lt (by omega)
  have o1 : Nat.choose (B + 1) (B + 1) = 1 := Nat.choose_self _
  have o2 : Nat.choose B B = 1 := Nat.choose_self _
  have hD : ((((Nat.choose ((A + 1) + (B + 1) + 1 - (A + 1 + 1)) (A + 1) : ℕ)) : ℚ) -
       (((Nat.choose ((A + 1) + (B + 1) + 1 - (A + 1 + 1)) (B + 1) : ℕ)) : ℚ)) *
        harmonic (A + 1 + 1) = -harmonic (A + 1 + 1) := by
    rw [eDl, z1, o1]
    push_cast
    ring
  have hF : ((((Nat.choose ((A + 1) + B + 1 - (A + 1 + 1)) (A + 1) : ℕ)) : ℚ) -
       (((Nat.choose ((A + 1) + B + 1 - (A + 1 + 1)) B : ℕ)) : ℚ)) *
        harmonic (A + 1 + 1) = -harmonic (A + 1 + 1) := by
    rw [eFl, z2, o2]
    push_cast
    ring
  rw [hmid, hD, hF]
  ring

private lemma b0_case (A : ℕ) : Lsum (A + 1) 0 = Rval (A + 1) 0 := by
  have hset : Finset.Icc 1 (A + 1 + 1) = insert 1 (Finset.Icc 2 (A + 1 + 1)) := by
    ext ν
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  have hnotmem : (1 : ℕ) ∉ Finset.Icc 2 (A + 1 + 1) := by simp
  have hH1 : harmonic 1 = 1 := by simp [harmonic_succ]
  have h1term : ((((Nat.choose ((A+1)+0+1-1) (A+1) : ℕ)) : ℚ) -
      (((Nat.choose ((A+1)+0+1-1) 0 : ℕ)) : ℚ)) * harmonic 1 = 0 := by
    have e : (A+1)+0+1-1 = A+1 := by omega
    rw [e, Nat.choose_self, Nat.choose_zero_right]
    simp
  have hrest : ∀ ν ∈ Finset.Icc 2 (A + 1 + 1),
      ((((Nat.choose ((A+1)+0+1-ν) (A+1) : ℕ)) : ℚ) -
       (((Nat.choose ((A+1)+0+1-ν) 0 : ℕ)) : ℚ)) * harmonic ν
      = -1 * harmonic ν := by
    intro ν hν
    have hν1 : 2 ≤ ν := (Finset.mem_Icc.mp hν).1
    have etop : (A+1)+0+1-ν = A+2-ν := by omega
    have hlt : A+2-ν < A+1 := by omega
    have z : Nat.choose (A+2-ν) (A+1) = 0 := Nat.choose_eq_zero_of_lt hlt
    have o : Nat.choose (A+2-ν) 0 = 1 := Nat.choose_zero_right _
    rw [etop, z, o]
    push_cast
    ring
  have htail : (∑ ν ∈ Finset.Icc 2 (A + 1 + 1),
        ((((Nat.choose ((A+1)+0+1-ν) (A+1) : ℕ)) : ℚ) -
         (((Nat.choose ((A+1)+0+1-ν) 0 : ℕ)) : ℚ)) * harmonic ν)
      = -1 * (∑ ν ∈ Finset.Icc 2 (A + 1 + 1), harmonic ν) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun ν hν => by rw [hrest ν hν])
  have hsplit : (∑ ν ∈ Finset.Icc 1 (A + 1 + 1), harmonic ν)
      = harmonic 1 + (∑ ν ∈ Finset.Icc 2 (A + 1 + 1), harmonic ν) := by
    rw [hset, Finset.sum_insert hnotmem]
  have hsum := sum_harmonic_Icc (A + 1 + 1)
  have r1 : (A+1)+0+2 = A+3 := by omega
  have r3 : (A+1)+1 = A+2 := by omega
  have hR : Rval (A + 1) 0 = (((A+3 : ℕ)) : ℚ) * (1 - harmonic (A+2)) := by
    simp only [Rval]
    rw [r1]
    have r2 : (0:ℕ)+1 = 1 := by omega
    rw [r2, r3, Nat.choose_one_right, hH1]
  have hL : Lsum (A+1) 0 = -1 * (∑ ν ∈ Finset.Icc 2 (A + 1 + 1), harmonic ν) := by
    simp only [Lsum]
    rw [hset, Finset.sum_insert hnotmem, h1term, zero_add]
    exact htail
  rw [hL, hR, ← r3]
  push_cast at hsum ⊢
  linear_combination -hsum + hsplit + hH1

private lemma key : ∀ (m a b : ℕ), b ≤ a → a + b = m → Lsum a b = Rval a b := by
  intro m a b
  induction m generalizing a b with
  | zero =>
    intro hle hsum
    have ha : a = 0 := by omega
    have hb : b = 0 := by omega
    subst ha
    subst hb
    rw [L_diag, R_diag]
  | succ m ih =>
    intro hle hsum
    cases a with
    | zero =>
      have hb : b = 0 := by omega
      subst hb
      rw [L_diag, R_diag]
    | succ A =>
      cases b with
      | zero => exact b0_case A
      | succ B =>
        by_cases heq : A = B
        · subst heq
          rw [L_diag, R_diag]
        · have hlt : B < A := by omega
          have h1 : Lsum A (B + 1) = Rval A (B + 1) :=
            ih A (B + 1) (by omega) (by omega)
          have h2 : Lsum (A + 1) B = Rval (A + 1) B :=
            ih (A + 1) B (by omega) (by omega)
          rw [L_add' A B hlt, R_add' A B, h1, h2]

/-! # Binomial-harmonic convolution identity
-/

/--
**Binomial-harmonic convolution identity.** Let $H_m = \sum_{i=1}^{m} 1/i$ denote the $m$-th
harmonic number. For natural numbers $k$ and $n$ with $1 \le k \le n$,
$$\sum_{\nu=1}^{n} \left(\binom{n+k-\nu-1}{n-1} - \binom{n+k-\nu-1}{k-1}\right) H_\nu =
\binom{n+k}{k} (H_k - H_n).$$

Proves `Wanted` entry `binomial_harmonic_convolution`.

Source: Horst Alzer and Man Kam Kwong, "Ramanujan and a Combinatorial
Identity Involving Harmonic Numbers," Journal of Integer Sequences 29 (2026),
Article 26.4.8, Theorem 1 (label T1), equation (1.1), lines 135–141,
https://cs.uwaterloo.ca/journals/JIS/VOL29/Alzer/alzer22.tex
-/
theorem binomial_harmonic_convolution (k n : ℕ) (hk : 0 < k) (hkn : k ≤ n) :
    ∑ ν ∈ Finset.Icc 1 n,
      (((Nat.choose (n + k - ν - 1) (n - 1) : ℚ) -
        (Nat.choose (n + k - ν - 1) (k - 1) : ℚ)) * harmonic ν) =
      (Nat.choose (n + k) k : ℚ) * (harmonic k - harmonic n) := by
  obtain ⟨b, rfl⟩ : ∃ b, k = b + 1 := ⟨k - 1, by omega⟩
  obtain ⟨a, rfl⟩ : ∃ a, n = a + 1 := ⟨n - 1, by omega⟩
  have hle : b ≤ a := by omega
  have key_h := key (a + b) a b hle rfl
  have hL : (∑ ν ∈ Finset.Icc 1 (a + 1),
        ((((Nat.choose ((a + 1) + (b + 1) - ν - 1) ((a + 1) - 1) : ℕ)) : ℚ) -
         ((((Nat.choose ((a + 1) + (b + 1) - ν - 1) ((b + 1) - 1) : ℕ)) : ℚ))) *
        harmonic ν) = Lsum a b := by
    simp only [Lsum]
    apply Finset.sum_congr rfl
    intro ν hν
    have e1 : (a + 1) + (b + 1) - ν - 1 = a + b + 1 - ν := by omega
    have e2 : (a + 1) - 1 = a := by omega
    have e3 : (b + 1) - 1 = b := by omega
    rw [e1, e2, e3]
  have hR : (((Nat.choose ((a + 1) + (b + 1)) (b + 1) : ℕ)) : ℚ) *
      (harmonic (b + 1) - harmonic (a + 1)) = Rval a b := by
    simp only [Rval]
    have e : (a + 1) + (b + 1) = a + b + 2 := by omega
    rw [e]
  rw [hL, hR]
  exact key_h

end MetaMathlibExt
