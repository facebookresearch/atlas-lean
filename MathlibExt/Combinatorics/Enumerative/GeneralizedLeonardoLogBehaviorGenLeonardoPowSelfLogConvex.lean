/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Real.Basic
public import MathlibExt.Combinatorics.Enumerative.GeneralizedLeonardoLogBehavior
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Log-convexity of the self-powers of generalized Leonardo numbers

For `k ≥ 1`, the sequence `(L_{k,n}^n)_{n ≥ 3}` of self-powers of the generalized Leonardo
numbers is log-convex. The main result is `genLeonardo_pow_self_logConvex`.

Source: Feng-Zhen Zhao, *The Log-Behavior of Some Sequences Related to the
Generalized Leonardo Numbers*, INTEGERS 24 (2024), Article A82, Theorem 5
(`integers-2024-A82-thm-5`).
-/

namespace MetaMathlibExt

namespace genLeonardo_pow_self_logConvex

private theorem genLeonardo_add_two (k : ℤ) (n : ℕ) :
    genLeonardo k (n + 2) = genLeonardo k (n + 1) + genLeonardo k n + k := rfl

private theorem genLeonardo_nonneg (k : ℤ) (hk : 0 ≤ k) : ∀ n : ℕ, 0 ≤ genLeonardo k n
  | 0 => by simp [genLeonardo]
  | 1 => by simp [genLeonardo]
  | n + 2 => by
    rw [genLeonardo_add_two]
    have h0 := genLeonardo_nonneg k hk n
    have h1 := genLeonardo_nonneg k hk (n + 1)
    linarith

private theorem genLeonardo_ge_one (k : ℤ) (hk : 0 ≤ k) : ∀ n : ℕ, 1 ≤ genLeonardo k n
  | 0 => by simp [genLeonardo]
  | 1 => by simp [genLeonardo]
  | n + 2 => by
    rw [genLeonardo_add_two]
    have h0 := genLeonardo_ge_one k hk n
    have h1 := genLeonardo_ge_one k hk (n + 1)
    linarith

private theorem genLeonardo_mono_succ (k : ℤ) (hk : 0 ≤ k) (n : ℕ) :
    genLeonardo k (n + 1) ≤ genLeonardo k (n + 2) := by
  rw [genLeonardo_add_two]
  have h := genLeonardo_nonneg k hk n
  linarith

private theorem L3 (K : ℤ) : genLeonardo K 3 = 2 * K + 3 := by
  have h2 : genLeonardo K 2 = 2 + K := rfl
  have h1 : genLeonardo K 1 = 1 := rfl
  have h3 : genLeonardo K 3 = genLeonardo K 2 + genLeonardo K 1 + K := rfl
  rw [h3, h2, h1]; ring

private theorem L4 (K : ℤ) : genLeonardo K 4 = 4 * K + 5 := by
  have h2 : genLeonardo K 2 = 2 + K := rfl
  have h3 := L3 K
  have h4 : genLeonardo K 4 = genLeonardo K 3 + genLeonardo K 2 + K := rfl
  rw [h4, h3, h2]; ring

private theorem L5 (K : ℤ) : genLeonardo K 5 = 7 * K + 8 := by
  have h3 := L3 K
  have h4 := L4 K
  have h5 : genLeonardo K 5 = genLeonardo K 4 + genLeonardo K 3 + K := rfl
  rw [h5, h4, h3]; ring

private theorem case_n4 (K : ℤ) (hK : 1 ≤ K) :
    genLeonardo K 4 ^ (2 * 4) ≤ genLeonardo K 3 ^ 3 * genLeonardo K 5 ^ 5 := by
  rw [L3 K, L4 K, L5 K]
  set a : ℤ := 2 * K + 3 with ha_def
  set b : ℤ := 4 * K + 5 with hb_def
  set c : ℤ := 7 * K + 8 with hc_def
  set A : ℤ := a * c with hA_def
  set D : ℤ := b ^ 2 - A with hD_def
  have ha_pos : (0:ℤ) < a := by rw [ha_def]; linarith
  have hb_pos : (0:ℤ) < b := by rw [hb_def]; linarith
  have hc_pos : (0:ℤ) < c := by rw [hc_def]; linarith
  have hA_pos : (0:ℤ) < A := by rw [hA_def]; exact mul_pos ha_pos hc_pos
  have hb2 : (0:ℤ) ≤ b ^ 2 := sq_nonneg b
  have hAD : A + D = b ^ 2 := by rw [hD_def]; ring
  have h3a : 3 * a ≤ c := by rw [ha_def, hc_def]; linarith
  have h4D : 4 * D ≤ A := by
    rw [hD_def, hA_def, ha_def, hb_def, hc_def]
    nlinarith [sq_nonneg K, hK]
  have h4le : 4 * (A + D) ≤ 5 * A := by linarith [h4D]
  have h4nn : (0:ℤ) ≤ 4 * (A + D) := by
    have : (0:ℤ) ≤ A + D := by rw [hAD]; exact hb2
    linarith
  have hpow := pow_le_pow_left₀ h4nn h4le 4
  have h256 : 256 * (A + D) ^ 4 ≤ 625 * A ^ 4 := by
    have e1 : (4 * (A + D)) ^ 4 = 256 * (A + D) ^ 4 := by ring
    have e2 : (5 * A) ^ 4 = 625 * A ^ 4 := by ring
    rw [e1, e2] at hpow
    linarith
  have hA4 : (0:ℤ) ≤ A ^ 4 := by positivity
  have h625 : 625 * A ^ 4 ≤ 3 * 256 * A ^ 4 := by
    have : (625:ℤ) ≤ 3 * 256 := by norm_num
    nlinarith [hA4, this, mul_le_mul_of_nonneg_right this hA4]
  have h3pow : (A + D) ^ 4 ≤ 3 * A ^ 4 := by
    have h256' : 256 * ((A + D) ^ 4) ≤ 256 * (3 * A ^ 4) := by linarith [h256, h625]
    have hpos : (0:ℤ) < 256 := by norm_num
    exact le_of_mul_le_mul_left h256' hpos
  have ha3c4 : (0:ℤ) ≤ a ^ 3 * c ^ 4 := by positivity
  have h3A : 3 * A ^ 4 ≤ a ^ 3 * c ^ 5 := by
    have e1 : 3 * A ^ 4 = (a ^ 3 * c ^ 4) * (3 * a) := by rw [hA_def]; ring
    have e2 : a ^ 3 * c ^ 5 = (a ^ 3 * c ^ 4) * c := by ring
    rw [e1, e2]
    exact mul_le_mul_of_nonneg_left h3a ha3c4
  have hpow2 : (b ^ (2 * 4)) = (A + D) ^ 4 := by
    have e : b ^ (2 * 4) = (b ^ 2) ^ 4 := by rw [pow_mul]
    rw [e, ← hAD]
  rw [hpow2]
  linarith [h3pow, h3A]

private theorem fib_cassini_neg (n : ℕ) :
    (Nat.fib (n + 2) : ℤ) ^ 2 - Nat.fib (n + 1) * Nat.fib (n + 3)
      = -((Nat.fib (n + 1) : ℤ) ^ 2 - Nat.fib n * Nat.fib (n + 2)) := by
  have h1 : (Nat.fib (n + 1 + 2) : ℤ) = Nat.fib (n + 1) + Nat.fib (n + 1 + 1) := by
    exact_mod_cast Nat.fib_add_two
  have h2 : (Nat.fib (n + 2) : ℤ) = Nat.fib n + Nat.fib (n + 1) := by
    exact_mod_cast Nat.fib_add_two
  have e1 : n + 1 + 2 = n + 3 := by omega
  have e2 : n + 1 + 1 = n + 2 := by omega
  rw [e1, e2] at h1
  linear_combination (Nat.fib (n + 2) : ℤ) * h2 - (Nat.fib (n + 1) : ℤ) * h1

private theorem fib_cassini_le_one (n : ℕ) :
    (Nat.fib (n + 1) : ℤ) ^ 2 - Nat.fib n * Nat.fib (n + 2) ≤ 1 := by
  have h : ∀ n : ℕ, -1 ≤ (Nat.fib (n + 1) : ℤ) ^ 2 - Nat.fib n * Nat.fib (n + 2)
      ∧ (Nat.fib (n + 1) : ℤ) ^ 2 - Nat.fib n * Nat.fib (n + 2) ≤ 1 := by
    intro n
    induction n with
    | zero => constructor <;> norm_num
    | succ n ih =>
      have h := fib_cassini_neg n
      have e1 : n + 1 + 1 = n + 2 := by omega
      have e2 : n + 1 + 2 = n + 3 := by omega
      rw [e1, e2]
      constructor <;> linarith [h, ih.1, ih.2]
  exact (h n).2

private theorem fib_linear_id (m : ℕ) :
    (Nat.fib (m + 4) : ℤ) + Nat.fib (m + 6) - 2 * Nat.fib (m + 5) = Nat.fib (m + 2) := by
  have h1 : (Nat.fib (m + 4 + 2) : ℤ) = Nat.fib (m + 4) + Nat.fib (m + 4 + 1) := by
    exact_mod_cast Nat.fib_add_two
  have h2 : (Nat.fib (m + 3 + 2) : ℤ) = Nat.fib (m + 3) + Nat.fib (m + 3 + 1) := by
    exact_mod_cast Nat.fib_add_two
  have h3 : (Nat.fib (m + 2 + 2) : ℤ) = Nat.fib (m + 2) + Nat.fib (m + 2 + 1) := by
    exact_mod_cast Nat.fib_add_two
  have e1 : m + 4 + 2 = m + 6 := by omega
  have e2 : m + 4 + 1 = m + 5 := by omega
  have e3 : m + 3 + 2 = m + 5 := by omega
  have e4 : m + 3 + 1 = m + 4 := by omega
  have e5 : m + 2 + 2 = m + 4 := by omega
  have e6 : m + 2 + 1 = m + 3 := by omega
  rw [e1, e2] at h1; rw [e3, e4] at h2; rw [e5, e6] at h3
  linear_combination h1 - h2 + h3

private theorem defect_le (K : ℤ) (hK : 0 ≤ K) (m : ℕ) :
    genLeonardo K (m + 4) ^ 2 - genLeonardo K (m + 3) * genLeonardo K (m + 5)
      ≤ (K + 1) ^ 2 * ((Nat.fib (m + 2) : ℤ) + 1) := by
  have ha := genLeonardo_add_eq_mul_fib K (m + 3)
  have hb := genLeonardo_add_eq_mul_fib K (m + 4)
  have hc := genLeonardo_add_eq_mul_fib K (m + 5)
  have e1 : m + 3 + 1 = m + 4 := by omega
  have e2 : m + 4 + 1 = m + 5 := by omega
  have e3 : m + 5 + 1 = m + 6 := by omega
  rw [e1] at ha; rw [e2] at hb; rw [e3] at hc
  have ha' : genLeonardo K (m + 3) = (1 + K) * Nat.fib (m + 4) - K := by linarith
  have hb' : genLeonardo K (m + 4) = (1 + K) * Nat.fib (m + 5) - K := by linarith
  have hc' : genLeonardo K (m + 5) = (1 + K) * Nat.fib (m + 6) - K := by linarith
  rw [ha', hb', hc']
  have hC : (Nat.fib (m + 5) : ℤ) ^ 2 - Nat.fib (m + 4) * Nat.fib (m + 6) ≤ 1 := by
    have h := fib_cassini_le_one (m + 4)
    have f1 : m + 4 + 1 = m + 5 := by omega
    have f2 : m + 4 + 2 = m + 6 := by omega
    rw [f1, f2] at h
    linarith
  have hF := fib_linear_id m
  have hF2 : (0:ℤ) ≤ Nat.fib (m + 2) := by positivity
  have hK1 : (0:ℤ) ≤ K + 1 := by linarith
  have h1C : (0:ℤ) ≤ 1 - ((Nat.fib (m + 5) : ℤ) ^ 2 - Nat.fib (m + 4) * Nat.fib (m + 6)) := by
    linarith
  have hsq : (0:ℤ) ≤ (K + 1) ^ 2 := by positivity
  have hprod1 := mul_nonneg hsq h1C
  have hprod2 := mul_nonneg hK1 hF2
  nlinarith [hF, hprod1, hprod2, ha, hb, hc]

private theorem fib_ge_three (n : ℕ) (hn : 4 ≤ n) : 3 ≤ Nat.fib n := by
  have h4 : Nat.fib 4 = 3 := by decide
  have hmono := Nat.fib_mono hn
  omega

private theorem ac_lower (K : ℤ) (hK : 0 ≤ K) (m : ℕ) :
    (K + 1) ^ 2 * (((Nat.fib (m + 4) : ℤ) - 1) * ((Nat.fib (m + 6) : ℤ) - 1))
      ≤ genLeonardo K (m + 3) * genLeonardo K (m + 5) := by
  have ha := genLeonardo_add_eq_mul_fib K (m + 3)
  have hc := genLeonardo_add_eq_mul_fib K (m + 5)
  have e1 : m + 3 + 1 = m + 4 := by omega
  have e3 : m + 5 + 1 = m + 6 := by omega
  rw [e1] at ha; rw [e3] at hc
  have ha' : genLeonardo K (m + 3) = (1 + K) * Nat.fib (m + 4) - K := by linarith
  have hc' : genLeonardo K (m + 5) = (1 + K) * Nat.fib (m + 6) - K := by linarith
  rw [ha', hc']
  have hK1 : (0:ℤ) ≤ K + 1 := by linarith
  have hF4 : (1:ℤ) ≤ Nat.fib (m + 4) := by
    have h : 3 ≤ Nat.fib (m + 4) := fib_ge_three (m + 4) (by omega)
    have hc : (3:ℤ) ≤ Nat.fib (m + 4) := by exact_mod_cast h
    linarith
  have hF6 : (1:ℤ) ≤ Nat.fib (m + 6) := by
    have h : 3 ≤ Nat.fib (m + 6) := fib_ge_three (m + 6) (by omega)
    have hc : (3:ℤ) ≤ Nat.fib (m + 6) := by exact_mod_cast h
    linarith
  have hA : (0:ℤ) ≤ (K + 1) * ((Nat.fib (m + 4) : ℤ) - 1) := by
    apply mul_nonneg hK1; linarith
  have hC : (0:ℤ) ≤ (K + 1) * ((Nat.fib (m + 6) : ℤ) - 1) := by
    apply mul_nonneg hK1; linarith
  nlinarith [hA, hC, mul_nonneg hK1 hK1]

private theorem fib_le_three_mul_two_back (m : ℕ) : Nat.fib (m + 5) ≤ 3 * Nat.fib (m + 3) := by
  have h1 : Nat.fib (m + 3 + 2) = Nat.fib (m + 3) + Nat.fib (m + 3 + 1) := Nat.fib_add_two
  have h2 : Nat.fib (m + 2 + 2) = Nat.fib (m + 2) + Nat.fib (m + 2 + 1) := Nat.fib_add_two
  have e1 : m + 3 + 2 = m + 5 := by omega
  have e2 : m + 3 + 1 = m + 4 := by omega
  have e3 : m + 2 + 2 = m + 4 := by omega
  have e4 : m + 2 + 1 = m + 3 := by omega
  rw [e1, e2] at h1; rw [e3, e4] at h2
  have hmono : Nat.fib (m + 2) ≤ Nat.fib (m + 3) := Nat.fib_mono (by omega)
  omega

private theorem fib_nine_ge_four_five (m : ℕ) : 4 * Nat.fib (m + 5) ≤ Nat.fib (m + 9) := by
  have h67 : Nat.fib (m + 5 + 2) = Nat.fib (m + 5) + Nat.fib (m + 5 + 1) := Nat.fib_add_two
  have h78 : Nat.fib (m + 6 + 2) = Nat.fib (m + 6) + Nat.fib (m + 6 + 1) := Nat.fib_add_two
  have h89 : Nat.fib (m + 7 + 2) = Nat.fib (m + 7) + Nat.fib (m + 7 + 1) := Nat.fib_add_two
  have e1 : m + 5 + 2 = m + 7 := by omega
  have e2 : m + 5 + 1 = m + 6 := by omega
  have e3 : m + 6 + 2 = m + 8 := by omega
  have e4 : m + 6 + 1 = m + 7 := by omega
  have e5 : m + 7 + 2 = m + 9 := by omega
  have e6 : m + 7 + 1 = m + 8 := by omega
  rw [e1, e2] at h67; rw [e3, e4] at h78; rw [e5, e6] at h89
  have m1 : Nat.fib (m + 5) ≤ Nat.fib (m + 6) := Nat.fib_mono (by omega)
  have m2 : Nat.fib (m + 6) ≤ Nat.fib (m + 7) := Nat.fib_mono (by omega)
  have m3 : Nat.fib (m + 7) ≤ Nat.fib (m + 8) := Nat.fib_mono (by omega)
  omega

private theorem lhs_step (m : ℕ) :
    ((m + 7 : ℕ) : ℤ) * (((Nat.fib (m + 5) : ℤ)) + 1)
      ≤ 4 * ((m + 5 : ℕ) : ℤ) * (((Nat.fib (m + 3) : ℤ)) + 1) := by
  rcases m with _ | m
  · have h5 : Nat.fib 5 = 5 := by decide
    have h3 : Nat.fib 3 = 2 := by decide
    norm_num [h5, h3]
  · have hF : (Nat.fib (m + 1 + 5) : ℤ) ≤ 3 * Nat.fib (m + 1 + 3) := by
      have h := fib_le_three_mul_two_back (m + 1)
      exact_mod_cast h
    have hm : (0:ℤ) ≤ ((m + 1 : ℕ) : ℤ) - 1 := by
      have : (1:ℤ) ≤ ((m + 1 : ℕ) : ℤ) := by exact_mod_cast Nat.le_add_left 1 m
      linarith
    have hX : (0:ℤ) ≤ (Nat.fib (m + 1 + 3) : ℤ) := by positivity
    have hprod := mul_nonneg hm hX
    push_cast at hF hprod ⊢
    nlinarith [hF, hprod]

private theorem rhs_step (m : ℕ) :
    4 * (((Nat.fib (m + 5) : ℤ) - 1) * (((Nat.fib (m + 7) : ℤ) - 1)))
      ≤ (((Nat.fib (m + 7) : ℤ) - 1)) * (((Nat.fib (m + 9) : ℤ) - 1)) := by
  have h9 : 4 * (Nat.fib (m + 5) : ℤ) ≤ Nat.fib (m + 9) := by
    have h := fib_nine_ge_four_five m
    exact_mod_cast h
  have hF7 : (0:ℤ) ≤ (Nat.fib (m + 7) : ℤ) - 1 := by
    have h : 3 ≤ Nat.fib (m + 7) := by
      have h4 : Nat.fib 4 = 3 := by decide
      have hm := Nat.fib_mono (show 4 ≤ m + 7 by omega)
      omega
    have hc : (3:ℤ) ≤ Nat.fib (m + 7) := by exact_mod_cast h
    linarith
  have h' : 4 * (((Nat.fib (m + 5) : ℤ) - 1)) ≤ ((Nat.fib (m + 9) : ℤ) - 1) := by linarith
  have heq : 4 * (((Nat.fib (m + 5) : ℤ) - 1) * (((Nat.fib (m + 7) : ℤ) - 1)))
      = (((Nat.fib (m + 7) : ℤ) - 1)) * (4 * (((Nat.fib (m + 5) : ℤ) - 1))) := by ring
  rw [heq]
  exact mul_le_mul_of_nonneg_left h' hF7

private theorem fib_key_ineq (m : ℕ) :
    2 * ((m + 5 : ℕ) : ℤ) * (((Nat.fib (m + 3) : ℤ)) + 1)
      ≤ (((Nat.fib (m + 5) : ℤ) - 1)) * (((Nat.fib (m + 7) : ℤ) - 1)) := by
  induction m using Nat.twoStepInduction with
  | zero =>
    have h3 : Nat.fib 3 = 2 := by decide
    have h5 : Nat.fib 5 = 5 := by decide
    have h7 : Nat.fib 7 = 13 := by decide
    norm_num [h3, h5, h7]
  | one =>
    have h4 : Nat.fib 4 = 3 := by decide
    have h6 : Nat.fib 6 = 8 := by decide
    have h8 : Nat.fib 8 = 21 := by decide
    norm_num [h4, h6, h8]
  | more m ih1 ih2 =>
    have hL := lhs_step m
    have hR := rhs_step m
    have e1 : m + 2 + 5 = m + 7 := by omega
    have e2 : m + 2 + 3 = m + 5 := by omega
    have e3 : m + 2 + 5 = m + 7 := by omega
    have e4 : m + 2 + 7 = m + 9 := by omega
    have goal_eq : (2 * (((m + 2 + 5 : ℕ)) : ℤ) * (((Nat.fib (m + 2 + 3) : ℤ)) + 1)
        ≤ (((Nat.fib (m + 2 + 5) : ℤ) - 1)) * (((Nat.fib (m + 2 + 7) : ℤ) - 1)))
        = (2 * (((m + 7 : ℕ)) : ℤ) * (((Nat.fib (m + 5) : ℤ)) + 1)
        ≤ (((Nat.fib (m + 7) : ℤ) - 1)) * (((Nat.fib (m + 9) : ℤ) - 1))) := by
      rw [e1, e2, e3, e4]
    rw [goal_eq]
    calc 2 * (((m + 7 : ℕ)) : ℤ) * (((Nat.fib (m + 5) : ℤ)) + 1)
        = 2 * ((((m + 7 : ℕ)) : ℤ) * (((Nat.fib (m + 5) : ℤ)) + 1)) := by ring
      _ ≤ 2 * (4 * ((m + 5 : ℕ) : ℤ) * (((Nat.fib (m + 3) : ℤ)) + 1)) :=
          mul_le_mul_of_nonneg_left hL (by norm_num)
      _ = 4 * (2 * ((m + 5 : ℕ) : ℤ) * (((Nat.fib (m + 3) : ℤ)) + 1)) := by ring
      _ ≤ 4 * (((Nat.fib (m + 5) : ℤ) - 1) * (((Nat.fib (m + 7) : ℤ) - 1))) :=
          mul_le_mul_of_nonneg_left ih1 (by norm_num)
      _ ≤ (((Nat.fib (m + 7) : ℤ) - 1)) * (((Nat.fib (m + 9) : ℤ) - 1)) := hR

private theorem mul_pow_le_of_le {a c : ℤ} (ha0 : 0 ≤ a) (hc0 : 0 ≤ c) (hac : a ≤ c) (m : ℕ) :
    (a * c) ^ (m + 5) ≤ a ^ (m + 4) * c ^ (m + 6) := by
  have hnn : (0:ℤ) ≤ a ^ (m + 4) * c ^ (m + 5) := by positivity
  have e1 : m + 5 = (m + 4) + 1 := by omega
  have e2 : m + 6 = (m + 5) + 1 := by omega
  have pa : a ^ (m + 5) = a ^ (m + 4) * a := by rw [e1, pow_succ]
  have pc : c ^ (m + 6) = c ^ (m + 5) * c := by rw [e2, pow_succ]
  calc (a * c) ^ (m + 5) = a ^ (m + 5) * c ^ (m + 5) := mul_pow a c (m + 5)
    _ = (a ^ (m + 4) * c ^ (m + 5)) * a := by rw [pa]; ring
    _ ≤ (a ^ (m + 4) * c ^ (m + 5)) * c := mul_le_mul_of_nonneg_left hac hnn
    _ = a ^ (m + 4) * c ^ (m + 6) := by rw [pc]; ring

private theorem two_mul_pow_le_of_two_le {a c : ℤ} (ha0 : 0 ≤ a) (hc0 : 0 ≤ c)
    (h2a : 2 * a ≤ c) (m : ℕ) :
    2 * (a * c) ^ (m + 5) ≤ a ^ (m + 4) * c ^ (m + 6) := by
  have hnn : (0:ℤ) ≤ a ^ (m + 4) * c ^ (m + 5) := by positivity
  have e1 : m + 5 = (m + 4) + 1 := by omega
  have e2 : m + 6 = (m + 5) + 1 := by omega
  have pa : a ^ (m + 5) = a ^ (m + 4) * a := by rw [e1, pow_succ]
  have pc : c ^ (m + 6) = c ^ (m + 5) * c := by rw [e2, pow_succ]
  calc 2 * (a * c) ^ (m + 5) = 2 * (a ^ (m + 5) * c ^ (m + 5)) := by rw [mul_pow]
    _ = (a ^ (m + 4) * c ^ (m + 5)) * (2 * a) := by rw [pa]; ring
    _ ≤ (a ^ (m + 4) * c ^ (m + 5)) * c := mul_le_mul_of_nonneg_left h2a hnn
    _ = a ^ (m + 4) * c ^ (m + 6) := by rw [pc]; ring

private theorem case_n5plus (K : ℤ) (hK1 : 1 ≤ K) (m : ℕ) :
    genLeonardo K (m + 5) ^ (2 * (m + 5))
      ≤ genLeonardo K (m + 4) ^ (m + 4) * genLeonardo K (m + 6) ^ (m + 6) := by
  have hK0 : (0:ℤ) ≤ K := by linarith
  set a : ℤ := genLeonardo K (m + 4) with ha_def
  set b : ℤ := genLeonardo K (m + 5) with hb_def
  set c : ℤ := genLeonardo K (m + 6) with hc_def
  set A : ℤ := a * c with hA_def
  set D : ℤ := b ^ 2 - A with hD_def
  have ha1 : (1:ℤ) ≤ a := by rw [ha_def]; exact genLeonardo_ge_one K hK0 (m + 4)
  have hb1 : (1:ℤ) ≤ b := by rw [hb_def]; exact genLeonardo_ge_one K hK0 (m + 5)
  have hc1 : (1:ℤ) ≤ c := by rw [hc_def]; exact genLeonardo_ge_one K hK0 (m + 6)
  have ha0 : (0:ℤ) ≤ a := by linarith
  have hb0 : (0:ℤ) ≤ b := by linarith
  have hc0 : (0:ℤ) ≤ c := by linarith
  have ha_pos : (0:ℤ) < a := by linarith
  have hc_pos : (0:ℤ) < c := by linarith
  have hA_pos : (0:ℤ) < A := by rw [hA_def]; exact mul_pos ha_pos hc_pos
  have hA0 : (0:ℤ) ≤ A := le_of_lt hA_pos
  have hb2 : (0:ℤ) ≤ b ^ 2 := sq_nonneg b
  have hAD : A + D = b ^ 2 := by rw [hD_def]; ring
  have hAD0 : (0:ℤ) ≤ A + D := by rw [hAD]; exact hb2
  -- monotonicity a ≤ b ≤ c
  have hab : a ≤ b := by
    have h := genLeonardo_mono_succ K hK0 (m + 3)
    have e1 : m + 3 + 1 = m + 4 := by omega
    have e2 : m + 3 + 2 = m + 5 := by omega
    rw [e1, e2] at h
    rw [ha_def, hb_def]
    exact h
  have hbc : b ≤ c := by
    have h := genLeonardo_mono_succ K hK0 (m + 4)
    have e1 : m + 4 + 1 = m + 5 := by omega
    have e2 : m + 4 + 2 = m + 6 := by omega
    rw [e1, e2] at h
    rw [hb_def, hc_def]
    exact h
  have hac : a ≤ c := le_trans hab hbc
  -- 2a ≤ c from recurrence
  have h2a : 2 * a ≤ c := by
    have hrec := genLeonardo_add_two K (m + 4)
    have e1 : m + 4 + 2 = m + 6 := by omega
    have e2 : m + 4 + 1 = m + 5 := by omega
    rw [e1, e2] at hrec
    rw [← ha_def, ← hb_def, ← hc_def] at hrec
    linarith [hab, hK0, hrec]
  -- b^(2N) = (A+D)^N
  have hpow2 : b ^ (2 * (m + 5)) = (A + D) ^ (m + 5) := by
    have e : b ^ (2 * (m + 5)) = (b ^ 2) ^ (m + 5) := by rw [pow_mul]
    rw [e, ← hAD]
  rw [hpow2]
  -- split on D
  rcases le_total D 0 with hDneg | hDnonneg
  · -- D ≤ 0: b^2 ≤ A
    have hb2le : b ^ 2 ≤ A := by rw [hD_def] at hDneg; linarith
    have h1 : (A + D) ^ (m + 5) ≤ A ^ (m + 5) := by
      rw [hAD]
      exact pow_le_pow_left₀ (sq_nonneg b) hb2le (m + 5)
    have h2 : A ^ (m + 5) ≤ a ^ (m + 4) * c ^ (m + 6) := by
      rw [hA_def]
      exact mul_pow_le_of_le ha0 hc0 hac m
    linarith [h1, h2]
  · -- 0 < D: use 2ND ≤ A
    have hD0' : (0:ℤ) ≤ D := hDnonneg
    -- 2 N D ≤ A via fib bounds
    have h2ND : 2 * (((m + 5 : ℕ) : ℤ)) * D ≤ A := by
      have hDle0 := defect_le K hK0 (m + 1)
      have d1 : m + 1 + 4 = m + 5 := by omega
      have d2 : m + 1 + 3 = m + 4 := by omega
      have d3 : m + 1 + 5 = m + 6 := by omega
      have d4 : m + 1 + 2 = m + 3 := by omega
      rw [d1, d2, d3, d4] at hDle0
      have hDle : D ≤ (K + 1) ^ 2 * ((Nat.fib (m + 3) : ℤ) + 1) := by
        rw [hD_def, hA_def, ha_def, hb_def, hc_def]
        linarith [hDle0]
      have hAle0 := ac_lower K hK0 (m + 1)
      have a1 : m + 1 + 4 = m + 5 := by omega
      have a2 : m + 1 + 6 = m + 7 := by omega
      have a3 : m + 1 + 3 = m + 4 := by omega
      have a4 : m + 1 + 5 = m + 6 := by omega
      rw [a1, a2, a3, a4] at hAle0
      have hAle :
          (K + 1) ^ 2 * (((Nat.fib (m + 5) : ℤ) - 1) * ((Nat.fib (m + 7) : ℤ) - 1)) ≤ A := by
        rw [hA_def, ha_def, hc_def]
        linarith [hAle0]
      have hFib := fib_key_ineq m
      have hK2 : (0:ℤ) ≤ (K + 1) ^ 2 := sq_nonneg _
      have hN : (0:ℤ) ≤ 2 * (((m + 5 : ℕ) : ℤ)) := by positivity
      calc 2 * (((m + 5 : ℕ) : ℤ)) * D
          ≤ 2 * (((m + 5 : ℕ) : ℤ)) * ((K + 1) ^ 2 * ((Nat.fib (m + 3) : ℤ) + 1)) :=
            mul_le_mul_of_nonneg_left hDle hN
        _ = (K + 1) ^ 2 * (2 * (((m + 5 : ℕ) : ℤ)) * (((Nat.fib (m + 3) : ℤ)) + 1)) := by ring
        _ ≤ (K + 1) ^ 2 * ((((Nat.fib (m + 5) : ℤ) - 1)) * (((Nat.fib (m + 7) : ℤ) - 1))) :=
            mul_le_mul_of_nonneg_left hFib hK2
        _ ≤ A := hAle
    -- (A+D)^N ≤ 2 A^N
    -- Bernoulli's inequality at `A + D` and `-D`
    have hPowLe : (A + D) ^ (m + 5) * (A - (((m + 5 : ℕ) : ℤ)) * D) ≤ A ^ (m + 5 + 1) := by
      have h := pow_add_mul_le_add_pow (a := A + D) (b := -D) hAD0 (by linarith) (m + 5 + 1)
      have e1 : A + D + -D = A := by ring
      have e2 : m + 5 + 1 - 1 = m + 5 := by omega
      rw [e1, e2] at h
      calc (A + D) ^ (m + 5) * (A - (((m + 5 : ℕ) : ℤ)) * D)
          = (A + D) ^ (m + 5 + 1) + ((m + 5 + 1 : ℕ) : ℤ) * (A + D) ^ (m + 5) * -D := by
            push_cast; ring
        _ ≤ A ^ (m + 5 + 1) := h
    have hA2 : A ≤ 2 * (A - (((m + 5 : ℕ) : ℤ)) * D) := by
      have h2 : 2 * ((((m + 5 : ℕ) : ℤ)) * D) ≤ A := by linarith [h2ND]
      linarith
    have hADnn : (0:ℤ) ≤ (A + D) ^ (m + 5) := pow_nonneg hAD0 (m + 5)
    have h1 : (A + D) ^ (m + 5) * A ≤ (A + D) ^ (m + 5) * (2 * (A - (((m + 5 : ℕ) : ℤ)) * D)) :=
      mul_le_mul_of_nonneg_left hA2 hADnn
    have h2 : (A + D) ^ (m + 5) * (2 * (A - (((m + 5 : ℕ) : ℤ)) * D))
        = 2 * ((A + D) ^ (m + 5) * (A - (((m + 5 : ℕ) : ℤ)) * D)) := by ring
    have h3 : 2 * ((A + D) ^ (m + 5) * (A - (((m + 5 : ℕ) : ℤ)) * D)) ≤ 2 * A ^ (m + 5 + 1) :=
      mul_le_mul_of_nonneg_left hPowLe (by norm_num)
    have h4 : (A + D) ^ (m + 5) * A ≤ 2 * A ^ (m + 5 + 1) := by linarith [h1, h2, h3]
    have h5 : (A + D) ^ (m + 5) * A ≤ (2 * A ^ (m + 5)) * A := by
      have e : A ^ (m + 5 + 1) = A ^ (m + 5) * A := pow_succ A (m + 5)
      rw [e] at h4
      linarith [h4]
    have h6 : (A + D) ^ (m + 5) ≤ 2 * A ^ (m + 5) := le_of_mul_le_mul_right h5 hA_pos
    have h7 : 2 * A ^ (m + 5) ≤ a ^ (m + 4) * c ^ (m + 6) := by
      have e : 2 * A ^ (m + 5) = 2 * (a * c) ^ (m + 5) := by rw [hA_def]
      rw [e]
      exact two_mul_pow_le_of_two_le ha0 hc0 h2a m
    linarith [h6, h7]
end genLeonardo_pow_self_logConvex

@[expose] public section

/-- **Log-convexity of the self-powers of generalized Leonardo numbers.** Let $k \ge 1$ be an
integer and let $L_{k,n}$ be the generalized Leonardo numbers. Then the sequence
$(L_{k,n}^n)_{n \ge 3}$ is log-convex: $L_{k,n}^{2n} \le L_{k,n-1}^{n-1} L_{k,n+1}^{n+1}$ for
every integer $n \ge 4$.

Source: Feng-Zhen Zhao, *The Log-Behavior of Some Sequences Related to the
Generalized Leonardo Numbers*, INTEGERS 24 (2024), Article A82, Theorem 5
(`integers-2024-A82-thm-5`). -/
public theorem genLeonardo_pow_self_logConvex (k : ℕ) (hk : 1 ≤ k) (n : ℕ)
    (hn : 4 ≤ n) :
    genLeonardo k n ^ (2 * n)
      ≤ genLeonardo k (n - 1) ^ (n - 1) * genLeonardo k (n + 1) ^ (n + 1) := by
  have hK1 : (1:ℤ) ≤ (k : ℤ) := by exact_mod_cast hk
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
  rcases m with _ | m
  · -- n = 0 + 4 = 4
    have e0 : 0 + 4 = 4 := rfl
    rw [e0]
    have e1 : 4 - 1 = 3 := rfl
    have e2 : 4 + 1 = 5 := rfl
    rw [e1, e2]
    exact genLeonardo_pow_self_logConvex.case_n4 (k : ℤ) hK1
  · -- n = (m+1) + 4 = m + 5
    have eM1 : ((m + 1) + 4) - 1 = m + 4 := by omega
    have eP1 : ((m + 1) + 4) + 1 = m + 6 := by omega
    have eN : (m + 1) + 4 = m + 5 := by omega
    rw [eM1, eP1, eN]
    exact genLeonardo_pow_self_logConvex.case_n5plus (k : ℤ) hK1 m

end

end MetaMathlibExt
