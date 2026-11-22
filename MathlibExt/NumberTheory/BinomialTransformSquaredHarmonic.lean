/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.NumberTheory.Harmonic.Defs
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.RingTheory.Binomial
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

@[expose] public section

namespace MetaMathlibExt

private lemma bridge (z : ℂ) (k : ℕ) :
    (descPochhammer ℂ k).eval z / ((k.factorial : ℕ) : ℂ) = Ring.choose z k := by
  have hmap : (descPochhammer ℤ k).map (RingHom.smulOneHom (R := ℤ) (S := ℂ)) =
      descPochhammer ℂ k := descPochhammer_map _ _
  have heval : (descPochhammer ℂ k).eval z = (descPochhammer ℤ k).smeval z := by
    conv_lhs => rw [← hmap, Polynomial.eval_map]
    rw [Polynomial.eval₂_smulOneHom_eq_smeval]
  have hchoose : (descPochhammer ℤ k).smeval z = k.factorial • Ring.choose z k :=
    Ring.descPochhammer_eq_factorial_smul_choose z k
  have hfact : ((k.factorial : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero k
  rw [heval, hchoose, nsmul_eq_mul]
  field_simp


private lemma choose_succ_absorb (z : ℂ) (k : ℕ) :
    ((k : ℂ) + 1) * Ring.choose z (k + 1) = (z - (k : ℂ)) * Ring.choose z k := by
  have h := Ring.choose_smul_choose (R := ℂ) z (n := k + 1) (k := k) (Nat.le_succ k)
  rw [Nat.choose_succ_self_right k] at h
  have hsub : k + 1 - k = 1 := by omega
  rw [hsub] at h
  rw [Ring.choose_one_right] at h
  rw [nsmul_eq_mul] at h
  have hcast : (((k + 1 : ℕ)) : ℂ) = (k : ℂ) + 1 := by push_cast; ring
  rw [hcast] at h
  linear_combination h


private lemma hsucc (n : ℕ) :
    ((harmonic (n + 1) : ℚ) : ℂ) = ((harmonic n : ℚ) : ℂ) + 1 / ((n : ℂ) + 1) := by
  rw [harmonic_succ]
  push_cast
  rw [one_div]

private lemma abel_step1 (x : ℂ) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), (-1 : ℂ) ^ k * Ring.choose x k * (((harmonic k : ℚ) : ℂ)) ^ 2
      = (-1 : ℂ) ^ n * Ring.choose (x - 1) n * (((harmonic n : ℚ) : ℂ)) ^ 2
        - ∑ k ∈ Finset.range n, (-1 : ℂ) ^ k * Ring.choose (x - 1) k *
          (2 * ((harmonic k : ℚ) : ℂ) / ((k : ℂ) + 1) + 1 / (((k : ℂ) + 1) ^ 2)) := by
  induction n with
  | zero =>
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, add_zero, sub_zero,
      pow_zero, Ring.choose_zero_right, one_mul, harmonic_zero, Rat.cast_zero,
      ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
  | succ n ih =>
    rw [Finset.sum_range_succ (fun k => (-1 : ℂ) ^ k * Ring.choose x k * (((harmonic k : ℚ) : ℂ)) ^
      2) (n + 1)]
    rw [Finset.sum_range_succ (fun k => (-1 : ℂ) ^ k * Ring.choose (x - 1) k * (2 * ((harmonic k :
      ℚ) : ℂ) / ((k : ℂ) + 1) + 1 / (((k : ℂ) + 1) ^ 2))) n]
    rw [ih]
    have hpascal : Ring.choose x (n + 1) =
        Ring.choose (x - 1) n + Ring.choose (x - 1) (n + 1) := by
      have h := Ring.choose_succ_succ (x - 1) n
      have hx : (x - 1) + 1 = x := by ring
      rw [hx] at h
      exact h
    have h1 := hsucc n
    have e1 : (-1 : ℂ) ^ (n + 1) = -(-1 : ℂ) ^ n := by rw [pow_succ]; ring
    have hn1 : ((n : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
    rw [hpascal, h1, e1]
    field_simp
    ring


private lemma harm_telescope (a : ℕ → ℂ) (n : ℕ) :
    ∑ k ∈ Finset.range n, ((a k - a (k + 1)) * ((harmonic k : ℚ) : ℂ))
      = -(a n * ((harmonic n : ℚ) : ℂ)) + ∑ k ∈ Finset.range n, (a (k + 1) / ((k : ℂ) + 1)) := by
  induction n with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty, add_zero, harmonic_zero, Rat.cast_zero,
      mul_zero, neg_zero]
  | succ n ih =>
    rw [Finset.sum_range_succ (fun k => (a k - a (k + 1)) * ((harmonic k : ℚ) : ℂ)) n]
    rw [Finset.sum_range_succ (fun k => a (k + 1) / ((k : ℂ) + 1)) n]
    rw [ih]
    have h1 := hsucc n
    have hn1 : ((n : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
    rw [h1]
    field_simp
    ring


private lemma absorb_key (x : ℂ) (k : ℕ) :
    x * ((-1 : ℂ) ^ k * Ring.choose (x - 1) k)
      = (((-1 : ℂ) ^ k * Ring.choose (x - 1) k - (-1 : ℂ) ^ (k + 1) * Ring.choose (x - 1) (k + 1)))
        * ((k : ℂ) + 1) := by
  have habs := choose_succ_absorb (x - 1) k
  have e1 : (-1 : ℂ) ^ (k + 1) = -(-1 : ℂ) ^ k := by rw [pow_succ]; ring
  rw [e1]
  linear_combination -((-1 : ℂ) ^ k) * habs

private lemma ring_pascal_sub (y : ℂ) (k : ℕ) (hk : 1 ≤ k) :
    Ring.choose (y + 1) k = Ring.choose y k + Ring.choose y (k - 1) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  have h := Ring.choose_succ_succ y j
  rw [add_comm (Ring.choose y j) (Ring.choose y (j + 1))] at h
  exact h

private lemma Lterm (x : ℂ) (n k : ℕ) (hk1 : 1 ≤ k) (hkn : k ≤ n) :
    Ring.choose (((n + 1 : ℕ) : ℂ) - x) k / ((k : ℂ) * (((Nat.choose (n + 1) k : ℕ)) : ℂ))
      = Ring.choose ((n : ℂ) - x) k / ((k : ℂ) * (Nat.choose n k : ℂ))
        - Ring.choose ((n : ℂ) - x) k / ((((n : ℂ) + 1)) * (Nat.choose n k : ℂ))
        + Ring.choose ((n : ℂ) - x) (k - 1) / ((((n : ℂ) + 1)) * (Nat.choose n (k - 1) : ℂ)) := by
  have hkpos : k ≠ 0 := by omega
  have hkk : ((k : ℂ)) ≠ 0 := by exact_mod_cast hkpos
  have hn1 : ((n : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  have hCnk : ((Nat.choose n k : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast Nat.choose_ne_zero hkn
  have hCnk1 : ((Nat.choose n (k - 1) : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast Nat.choose_ne_zero (by omega : k - 1 ≤ n)
  have hCn1k : ((Nat.choose (n + 1) k : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast Nat.choose_ne_zero (by omega : k ≤ n + 1)
  have hsub : k - 1 + 1 = k := by omega
  have hY : ((n : ℂ) - x) + 1 = (((n + 1 : ℕ)) : ℂ) - x := by push_cast; ring
  have hpascal : Ring.choose (((n + 1 : ℕ) : ℂ) - x) k
      = Ring.choose ((n : ℂ) - x) k + Ring.choose ((n : ℂ) - x) (k - 1) := by
    conv_lhs => rw [← hY]
    exact ring_pascal_sub ((n : ℂ) - x) k hk1
  have hadd := Nat.add_one_mul_choose_eq n (k - 1)
  rw [hsub] at hadd
  have haddC : (((n : ℂ) + 1)) * (Nat.choose n (k - 1) : ℂ)
      = (Nat.choose (n + 1) k : ℂ) * (k : ℂ) := by
    have hcast1 : (((n + 1 : ℕ)) : ℂ) = ((n : ℂ) + 1) := by push_cast; ring
    have haddC' : (((n + 1 : ℕ)) : ℂ) * (Nat.choose n (k - 1) : ℂ)
        = (Nat.choose (n + 1) k : ℂ) * ((k : ℕ) : ℂ) := by exact_mod_cast hadd
    rw [hcast1] at haddC'
    exact haddC'
  have hmul := Nat.choose_mul_succ_eq n k
  have hcast_sub : ((((n + 1 - k : ℕ))) : ℂ) = ((n : ℂ) + 1) - (k : ℂ) := by
    rw [Nat.cast_sub (by omega : k ≤ n + 1)]
    push_cast
    ring
  have hmulC : (Nat.choose n k : ℂ) * (((n : ℂ) + 1))
      = (Nat.choose (n + 1) k : ℂ) * ((((n : ℂ) + 1) - (k : ℂ))) := by
    have hcast1 : (((n + 1 : ℕ)) : ℂ) = ((n : ℂ) + 1) := by push_cast; ring
    have hmulC' : (Nat.choose n k : ℂ) * ((((n + 1 : ℕ))) : ℂ)
        = (Nat.choose (n + 1) k : ℂ) * ((((n + 1 - k : ℕ))) : ℂ) := by exact_mod_cast hmul
    rw [hcast1, hcast_sub] at hmulC'
    exact hmulC'
  rw [hpascal]
  field_simp
  linear_combination
    (Ring.choose ((n : ℂ) - x) k * (Nat.choose n (k - 1) : ℂ)) * hmulC
    + (Ring.choose ((n : ℂ) - x) (k - 1) * (Nat.choose n k : ℂ)) * haddC


private lemma icc_telescope (g : ℕ → ℂ) (n : ℕ) :
    ∑ k ∈ Finset.Icc 1 n, (g (k - 1) - g k) = g 0 - g n := by
  induction n with
  | zero =>
    simp only [Finset.Icc_eq_empty (by omega : ¬ (1 : ℕ) ≤ 0), Finset.sum_empty, sub_self]
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1), ih]
    have hsub : n + 1 - 1 = n := by omega
    rw [hsub]
    ring


private lemma Lrec (x : ℂ) (n : ℕ) :
    ∑ k ∈ Finset.Icc 1 (n + 1), Ring.choose ((((n + 1 : ℕ)) : ℂ) - x) k / ((k : ℂ) * (Nat.choose (n
      + 1) k : ℂ))
      = (∑ k ∈ Finset.Icc 1 n, Ring.choose (((n : ℂ)) - x) k / ((k : ℂ) * (Nat.choose n k : ℂ)))
        + (1 + Ring.choose ((n : ℂ) - x) (n + 1)) / ((n : ℂ) + 1) := by
  have hn1 : ((n : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  have hsplit : ∑ k ∈ Finset.Icc 1 (n + 1), Ring.choose ((((n + 1 : ℕ)) : ℂ) - x) k / ((k : ℂ) *
    (Nat.choose (n + 1) k : ℂ))
      = (∑ k ∈ Finset.Icc 1 n, Ring.choose ((((n + 1 : ℕ)) : ℂ) - x) k / ((k : ℂ) * (Nat.choose (n
        + 1) k : ℂ)))
        + Ring.choose ((((n + 1 : ℕ)) : ℂ) - x) (n + 1) / ((((n + 1 : ℕ)) : ℂ) * (Nat.choose (n +
          1) (n + 1) : ℂ)) :=
    Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1) _
  rw [hsplit]
  have hterm : ∀ k ∈ Finset.Icc 1 n,
      Ring.choose ((((n + 1 : ℕ)) : ℂ) - x) k / ((k : ℂ) * (Nat.choose (n + 1) k : ℂ))
        = Ring.choose (((n : ℂ)) - x) k / ((k : ℂ) * (Nat.choose n k : ℂ))
          + (1 / ((n : ℂ) + 1)) * (Ring.choose ((n : ℂ) - x) (k - 1) / (Nat.choose n (k - 1) : ℂ) -
            Ring.choose ((n : ℂ) - x) k / (Nat.choose n k : ℂ)) := by
    intro k hk
    have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
    have hkn : k ≤ n := (Finset.mem_Icc.mp hk).2
    have hkk : ((k : ℂ)) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
    have hCnk : ((Nat.choose n k : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.choose_ne_zero hkn
    have hCnk1 : ((Nat.choose n (k - 1) : ℕ) : ℂ) ≠ 0 := by
      exact_mod_cast Nat.choose_ne_zero (by omega : k - 1 ≤ n)
    have h := Lterm x n k hk1 hkn
    rw [h]
    field_simp
    ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, ← Finset.mul_sum]
  have htele := icc_telescope (fun j => Ring.choose ((n : ℂ) - x) j / (Nat.choose n j : ℂ)) n
  rw [htele]
  have hg0 : Ring.choose ((n : ℂ) - x) 0 / (Nat.choose n 0 : ℂ) = 1 := by
    simp only [Ring.choose_zero_right, Nat.choose_zero_right, Nat.cast_one, div_one]
  have hgn1 : (Nat.choose (n + 1) (n + 1) : ℂ) = 1 := by simp only [Nat.choose_self, Nat.cast_one]
  rw [hg0, hgn1]
  have hY : ((n : ℂ) - x) + 1 = ((((n + 1 : ℕ))) : ℂ) - x := by push_cast; ring
  have hpascal_top : Ring.choose ((((n + 1 : ℕ)) : ℂ) - x) (n + 1)
      = Ring.choose ((n : ℂ) - x) (n + 1) + Ring.choose ((n : ℂ) - x) n := by
    conv_lhs => rw [← hY]
    have h := Ring.choose_succ_succ ((n : ℂ) - x) n
    rw [add_comm (Ring.choose ((n : ℂ) - x) n) (Ring.choose ((n : ℂ) - x) (n + 1))] at h
    exact h
  have hCn : (Nat.choose n n : ℂ) = 1 := by simp only [Nat.choose_self, Nat.cast_one]
  rw [hpascal_top, hCn]
  have hcast : ((((n + 1 : ℕ))) : ℂ) = ((n : ℂ) + 1) := by push_cast; ring
  rw [hcast]
  field_simp
  ring


private lemma negOnePow_smul (k : ℕ) (y : ℂ) :
    (↑k : ℤ).negOnePow • y = (-1 : ℂ) ^ k * y := by
  rw [Units.smul_def, zsmul_eq_mul, Int.cast_negOnePow_natCast]

private lemma choose_sub_eq (x : ℂ) (n : ℕ) :
    Ring.choose ((n : ℂ) - x) (n + 1) = (-1 : ℂ) ^ (n + 1) * Ring.choose x (n + 1) := by
  have hneg := Ring.choose_neg (x - (n : ℂ)) (n + 1)
  have hneg2 : - (x - (n : ℂ)) = (n : ℂ) - x := by ring
  rw [hneg2] at hneg
  have harg : (x - (n : ℂ)) + ((n + 1 : ℕ) : ℂ) - 1 = x := by push_cast; ring
  rw [harg] at hneg
  rw [hneg]
  exact (negOnePow_smul (n + 1) (Ring.choose x (n + 1))).symm ▸ rfl


private lemma choose_absorb_right (x : ℂ) (n : ℕ) :
    (((n : ℂ) + 1)) * Ring.choose x (n + 1) = x * Ring.choose (x - 1) n := by
  have hle : 1 ≤ n + 1 := Nat.le_add_left 1 n
  have h := Ring.choose_smul_choose (R := ℂ) x (n := n + 1) (k := 1) hle
  have hchoose1 : Nat.choose (n + 1) 1 = n + 1 := Nat.choose_one_right (n + 1)
  rw [hchoose1] at h
  have hsub : n + 1 - 1 = n := Nat.add_sub_cancel n 1
  rw [hsub] at h
  rw [Ring.choose_one_right] at h
  rw [nsmul_eq_mul] at h
  have hcast : ((((n + 1 : ℕ))) : ℂ) = ((n : ℂ) + 1) := by push_cast; ring
  rw [hcast, Nat.cast_one] at h
  linear_combination h


private lemma pointwise_C (x : ℂ) (hx : x ≠ 0) (n : ℕ) :
    Ring.choose ((n : ℂ) - x) (n + 1)
      = (-1 : ℂ) ^ n * Ring.choose (x - 1) n + (-1 : ℂ) ^ (n + 1) * Ring.choose (x - 1) (n + 1)
        + 2 * (((n : ℂ) + 1)) * (((-1 : ℂ) ^ (n + 1) * Ring.choose (x - 1) (n + 1) - (-1 : ℂ) ^ n *
          Ring.choose (x - 1) n)) / x := by
  have hsub := choose_sub_eq x n
  have hpascal : Ring.choose x (n + 1) = Ring.choose (x - 1) n + Ring.choose (x - 1) (n + 1) := by
    have h := Ring.choose_succ_succ (x - 1) n
    have hx : (x - 1) + 1 = x := by ring
    rw [hx] at h
    exact h
  have habs := choose_absorb_right x n
  rw [hpascal] at habs
  have e1 : (-1 : ℂ) ^ (n + 1) = -(-1 : ℂ) ^ n := by rw [pow_succ]; ring
  rw [hsub, hpascal, e1]
  field_simp
  linear_combination 2 * habs


private lemma reciprocal_id (x : ℂ) (hx : x ≠ 0) (n : ℕ) :
    ∑ k ∈ Finset.Icc 1 n, Ring.choose (((n : ℂ)) - x) k / ((k : ℂ) * (Nat.choose n k : ℂ))
      = (∑ k ∈ Finset.Icc 1 n, (((-1 : ℂ) ^ (k - 1) * Ring.choose (x - 1) (k - 1) + (-1 : ℂ) ^ k *
        Ring.choose (x - 1) k + 1) / (k : ℂ)))
        + 2 * (((-1 : ℂ) ^ n * Ring.choose (x - 1) n - 1)) / x := by
  induction n with
  | zero =>
    simp only [Finset.Icc_eq_empty (by omega : ¬ (1 : ℕ) ≤ 0), Finset.sum_empty,
      pow_zero, Ring.choose_zero_right, one_mul, sub_self, mul_zero, zero_div, add_zero]
  | succ n ih =>
    have hL := Lrec x n
    have hcast : ((((n + 1 : ℕ))) : ℂ) = ((n : ℂ) + 1) := by push_cast; ring
    have hS : ∑ k ∈ Finset.Icc 1 (n + 1), (((-1 : ℂ) ^ (k - 1) * Ring.choose (x - 1) (k - 1) + (-1
      : ℂ) ^ k * Ring.choose (x - 1) k + 1) / (k : ℂ))
        = (∑ k ∈ Finset.Icc 1 n, (((-1 : ℂ) ^ (k - 1) * Ring.choose (x - 1) (k - 1) + (-1 : ℂ) ^ k
          * Ring.choose (x - 1) k + 1) / (k : ℂ)))
          + (((-1 : ℂ) ^ n * Ring.choose (x - 1) n + (-1 : ℂ) ^ (n + 1) * Ring.choose (x - 1) (n +
            1) + 1) / ((n : ℂ) + 1)) := by
      have h := Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1) (fun k => (((-1 : ℂ) ^ (k - 1) *
        Ring.choose (x - 1) (k - 1) + (-1 : ℂ) ^ k * Ring.choose (x - 1) k + 1) / (k : ℂ)))
      rw [hcast] at h
      rw [h]
      have hsub : n + 1 - 1 = n := by omega
      rw [hsub]
    rw [hS, hL, ih]
    have hC := pointwise_C x hx n
    have hn1 : ((n : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
    rw [hC]
    field_simp
    ring


private lemma range_to_Icc_zero (f : ℕ → ℂ) (hf0 : f 0 = 0) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), f k = ∑ k ∈ Finset.Icc 1 n, f k := by
  induction n with
  | zero =>
    have h0 : Finset.Icc 1 0 = (∅ : Finset ℕ) := by decide
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, add_zero, hf0, h0]
  | succ n ih =>
    rw [Finset.sum_range_succ (fun k => f k) (n + 1)]
    rw [ih]
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1) (fun k => f k)]

private lemma range_to_Icc_shift (F : ℕ → ℂ) (n : ℕ) :
    ∑ k ∈ Finset.range n, F k = ∑ k ∈ Finset.Icc 1 n, F (k - 1) := by
  induction n with
  | zero =>
    have h0 : Finset.Icc 1 0 = (∅ : Finset ℕ) := by decide
    simp only [Finset.range_zero, Finset.sum_empty, h0]
  | succ n ih =>
    rw [Finset.sum_range_succ _ n]
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1) (fun k => F (k - 1))]
    rw [ih]
    have hsub : n + 1 - 1 = n := by omega
    rw [hsub]

private lemma harm_eq_sum (n : ℕ) :
    ((harmonic n : ℚ) : ℂ) = ∑ k ∈ Finset.Icc 1 n, (1 / (k : ℂ)) := by
  rw [harmonic_eq_sum_Icc]
  rw [Rat.cast_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Rat.cast_inv, Rat.cast_natCast, one_div]


private lemma termwise_mul (x : ℂ) (k : ℕ) (Hk : ℂ) :
    x * ((-1 : ℂ) ^ k * Ring.choose (x - 1) k * (2 * Hk / ((k : ℂ) + 1) + 1 / (((k : ℂ) + 1) ^ 2)))
      = 2 * (((-1 : ℂ) ^ k * Ring.choose (x - 1) k - (-1 : ℂ) ^ (k + 1) * Ring.choose (x - 1) (k +
        1)) * Hk)
        + ((-1 : ℂ) ^ k * Ring.choose (x - 1) k - (-1 : ℂ) ^ (k + 1) * Ring.choose (x - 1) (k + 1))
          / ((k : ℂ) + 1) := by
  have hk1 : ((k : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
  have key := absorb_key x k
  field_simp
  linear_combination (2 * Hk * (((k : ℂ) + 1)) + 1) * key

private lemma abel_Icc (x : ℂ) (n : ℕ) :
    ∑ k ∈ Finset.Icc 1 n, (-1 : ℂ) ^ k * Ring.choose x k * (((harmonic k : ℚ) : ℂ)) ^ 2
      = (-1 : ℂ) ^ n * Ring.choose (x - 1) n * (((harmonic n : ℚ) : ℂ)) ^ 2
        - ∑ k ∈ Finset.range n, (-1 : ℂ) ^ k * Ring.choose (x - 1) k *
          (2 * ((harmonic k : ℚ) : ℂ) / ((k : ℂ) + 1) + 1 / (((k : ℂ) + 1) ^ 2)) := by
  have h_abel := abel_step1 x n
  have hf0 : (fun k => (-1 : ℂ) ^ k * Ring.choose x k * (((harmonic k : ℚ) : ℂ)) ^ 2) 0 = 0 := by
    simp only [pow_zero, Ring.choose_zero_right, one_mul, harmonic_zero, Rat.cast_zero,
      ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero]
  have h_range := range_to_Icc_zero (fun k => (-1 : ℂ) ^ k * Ring.choose x k * (((harmonic k : ℚ) :
    ℂ)) ^ 2) hf0 n
  rw [h_range] at h_abel
  exact h_abel

private lemma T1_mul (x : ℂ) (n : ℕ) :
    x * (∑ k ∈ Finset.range n, (-1 : ℂ) ^ k * Ring.choose (x - 1) k *
        (2 * ((harmonic k : ℚ) : ℂ) / ((k : ℂ) + 1) + 1 / (((k : ℂ) + 1) ^ 2)))
      = 2 * (∑ k ∈ Finset.range n, (((-1 : ℂ) ^ k * Ring.choose (x - 1) k - (-1 : ℂ) ^ (k + 1) *
        Ring.choose (x - 1) (k + 1)) * ((harmonic k : ℚ) : ℂ)))
        + ∑ k ∈ Finset.range n, (((-1 : ℂ) ^ k * Ring.choose (x - 1) k - (-1 : ℂ) ^ (k + 1) *
          Ring.choose (x - 1) (k + 1)) / ((k : ℂ) + 1)) := by
  rw [Finset.mul_sum]
  have hterm : ∀ k ∈ Finset.range n,
      x * ((-1 : ℂ) ^ k * Ring.choose (x - 1) k * (2 * ((harmonic k : ℚ) : ℂ) / ((k : ℂ) + 1) + 1 /
        (((k : ℂ) + 1) ^ 2)))
        = 2 * (((-1 : ℂ) ^ k * Ring.choose (x - 1) k - (-1 : ℂ) ^ (k + 1) * Ring.choose (x - 1) (k
          + 1)) * ((harmonic k : ℚ) : ℂ))
          + (((-1 : ℂ) ^ k * Ring.choose (x - 1) k - (-1 : ℂ) ^ (k + 1) * Ring.choose (x - 1) (k +
            1)) / ((k : ℂ) + 1)) := by
    intro k hk
    exact termwise_mul x k ((harmonic k : ℚ) : ℂ)
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, ← Finset.mul_sum]

private lemma S1_eq (x : ℂ) (n : ℕ) :
    ∑ k ∈ Finset.range n, (((-1 : ℂ) ^ k * Ring.choose (x - 1) k - (-1 : ℂ) ^ (k + 1) * Ring.choose
      (x - 1) (k + 1)) * ((harmonic k : ℚ) : ℂ))
      = -(((-1 : ℂ) ^ n * Ring.choose (x - 1) n) * ((harmonic n : ℚ) : ℂ))
        + ∑ k ∈ Finset.range n, (((-1 : ℂ) ^ (k + 1) * Ring.choose (x - 1) (k + 1)) / ((k : ℂ) +
          1)) := by
  have h := harm_telescope (fun k => (-1 : ℂ) ^ k * Ring.choose (x - 1) k) n
  exact h

private lemma S4_eq (x : ℂ) (n : ℕ) :
    2 * (∑ k ∈ Finset.range n, (((-1 : ℂ) ^ (k + 1) * Ring.choose (x - 1) (k + 1)) / ((k : ℂ) + 1)))
      + ∑ k ∈ Finset.range n, (((-1 : ℂ) ^ k * Ring.choose (x - 1) k - (-1 : ℂ) ^ (k + 1) *
        Ring.choose (x - 1) (k + 1)) / ((k : ℂ) + 1))
      = ∑ k ∈ Finset.range n, (((-1 : ℂ) ^ k * Ring.choose (x - 1) k + (-1 : ℂ) ^ (k + 1) *
        Ring.choose (x - 1) (k + 1)) / ((k : ℂ) + 1)) := by
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  ring

private lemma S4_to_S5 (x : ℂ) (n : ℕ) :
    ∑ k ∈ Finset.range n, (((-1 : ℂ) ^ k * Ring.choose (x - 1) k + (-1 : ℂ) ^ (k + 1) * Ring.choose
      (x - 1) (k + 1)) / ((k : ℂ) + 1))
      = ∑ k ∈ Finset.Icc 1 n, (((-1 : ℂ) ^ (k - 1) * Ring.choose (x - 1) (k - 1) + (-1 : ℂ) ^ k *
        Ring.choose (x - 1) k) / (k : ℂ)) := by
  have hshift := range_to_Icc_shift (fun k => (((-1 : ℂ) ^ k * Ring.choose (x - 1) k + (-1 : ℂ) ^
    (k + 1) * Ring.choose (x - 1) (k + 1)) / ((k : ℂ) + 1))) n
  rw [hshift]
  apply Finset.sum_congr rfl
  intro k hk
  have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
  have hsub1 : k - 1 + 1 = k := by omega
  have hcast : ((((k - 1 : ℕ)) : ℂ) + 1) = (k : ℂ) := by
    have hsub : ((((k - 1 : ℕ))) : ℂ) = (k : ℂ) - 1 := by
      have h := Nat.cast_sub (R := ℂ) hk1
      simp only [Nat.cast_one] at h
      exact h
    linear_combination hsub
  change (((-1 : ℂ) ^ (k - 1) * Ring.choose (x - 1) (k - 1) + (-1 : ℂ) ^ (k - 1 + 1) * Ring.choose
    (x - 1) (k - 1 + 1)) / ((((k - 1 : ℕ)) : ℂ) + 1))
      = (((-1 : ℂ) ^ (k - 1) * Ring.choose (x - 1) (k - 1) + (-1 : ℂ) ^ k * Ring.choose (x - 1) k)
        / (k : ℂ))
  rw [hsub1, hcast]

private lemma S6_eq (x : ℂ) (n : ℕ) :
    ∑ k ∈ Finset.Icc 1 n, (((-1 : ℂ) ^ (k - 1) * Ring.choose (x - 1) (k - 1) + (-1 : ℂ) ^ k *
      Ring.choose (x - 1) k + 1) / (k : ℂ))
      = (∑ k ∈ Finset.Icc 1 n, (((-1 : ℂ) ^ (k - 1) * Ring.choose (x - 1) (k - 1) + (-1 : ℂ) ^ k *
        Ring.choose (x - 1) k) / (k : ℂ)))
        + ((harmonic n : ℚ) : ℂ) := by
  have hsplit : ∀ k ∈ Finset.Icc 1 n,
      (((-1 : ℂ) ^ (k - 1) * Ring.choose (x - 1) (k - 1) + (-1 : ℂ) ^ k * Ring.choose (x - 1) k +
        1) / (k : ℂ))
        = (((-1 : ℂ) ^ (k - 1) * Ring.choose (x - 1) (k - 1) + (-1 : ℂ) ^ k * Ring.choose (x - 1)
          k) / (k : ℂ)) + (1 / (k : ℂ)) := by
    intro k hk
    ring
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib]
  have hH := harm_eq_sum n
  rw [hH]

private lemma Lmul_eq (x : ℂ) (hx : x ≠ 0) (n : ℕ) :
    x * (∑ k ∈ Finset.Icc 1 n, Ring.choose (((n : ℂ)) - x) k / ((k : ℂ) * (Nat.choose n k : ℂ)))
      = x * (∑ k ∈ Finset.Icc 1 n, (((-1 : ℂ) ^ (k - 1) * Ring.choose (x - 1) (k - 1) + (-1 : ℂ) ^
        k * Ring.choose (x - 1) k + 1) / (k : ℂ)))
        + 2 * (((-1 : ℂ) ^ n * Ring.choose (x - 1) n - 1)) := by
  have hL := reciprocal_id x hx n
  field_simp at hL
  linear_combination hL

private lemma general_id (x : ℂ) (hx : x ≠ 0) (n : ℕ) :
    ∑ k ∈ Finset.Icc 1 n, (-1 : ℂ) ^ k * Ring.choose x k * (((harmonic k : ℚ) : ℂ)) ^ 2
      = (-1 : ℂ) ^ n * Ring.choose (x - 1) n * ((((harmonic n : ℚ) : ℂ)) ^ 2 + 2 * ((harmonic n :
        ℚ) : ℂ) / x + 2 / x ^ 2)
        + ((harmonic n : ℚ) : ℂ) / x - 2 / x ^ 2
        - (1 / x) * (∑ k ∈ Finset.Icc 1 n, Ring.choose (((n : ℂ)) - x) k / ((k : ℂ) * (Nat.choose n
          k : ℂ))) := by
  have h_abel := abel_Icc x n
  have h_T1 := T1_mul x n
  have h_S1 := S1_eq x n
  have h_S4 := S4_eq x n
  have h_S4S5 := S4_to_S5 x n
  have h_S6 := S6_eq x n
  have h_L := Lmul_eq x hx n
  have hx2 : x ^ 2 ≠ 0 := pow_ne_zero 2 hx
  apply mul_left_cancel₀ hx2
  field_simp
  linear_combination (x ^ 2) * h_abel + (-x) * h_T1 + (-2 * x) * h_S1 + (-x) * h_S4 + (-x) * h_S4S5
    + (x) * h_S6 + (1) * h_L

private lemma choose_neg_s (s : ℂ) (k : ℕ) :
    Ring.choose (-s) k = (-1 : ℂ) ^ k * Ring.choose (s + (k : ℂ) - 1) k := by
  have hneg := Ring.choose_neg s k
  have harg : s + ((k : ℕ) : ℂ) - 1 = s + (k : ℂ) - 1 := rfl
  rw [harg, negOnePow_smul] at hneg
  exact hneg

private lemma choose_absorb_sub (z : ℂ) (k : ℕ) (hk : 1 ≤ k) :
    (k : ℂ) * Ring.choose z k = (z - (((k - 1 : ℕ)) : ℂ)) * Ring.choose z (k - 1) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  have habs := choose_succ_absorb z j
  have hcast : ((((j + 1 : ℕ))) : ℂ) = ((j : ℂ) + 1) := by push_cast; ring
  have hgoal : ((((j + 1 : ℕ))) : ℂ) * Ring.choose z (j + 1) = (z - (j : ℂ)) * Ring.choose z j := by
    rw [hcast]
    exact habs
  exact hgoal

private lemma absorb_s_eq (s : ℂ) (k : ℕ) (hk : 1 ≤ k) :
    (k : ℂ) * Ring.choose (s + (k : ℂ) - 1) k = s * Ring.choose (s + (k : ℂ) - 1) (k - 1) := by
  have habs := choose_absorb_sub (s + (k : ℂ) - 1) k hk
  have hsub : ((((k - 1 : ℕ))) : ℂ) = (k : ℂ) - 1 := by
    have h := Nat.cast_sub (R := ℂ) hk
    simp only [Nat.cast_one] at h
    exact h
  have hz : (s + (k : ℂ) - 1) - ((((k - 1 : ℕ))) : ℂ) = s := by
    rw [hsub]
    ring
  rw [hz] at habs
  exact habs

private lemma residual_term (s : ℂ) (n k : ℕ) (hk1 : 1 ≤ k) (hkn : k ≤ n) :
    Ring.choose (-s) k / ((k : ℂ) * (Nat.choose n k : ℂ))
      = s * (((-1 : ℂ) ^ k * Ring.choose (s + (k : ℂ) - 1) (k - 1)) / ((k : ℂ) ^ 2 * (Nat.choose n
        k : ℂ))) := by
  have hkk : ((k : ℂ)) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
  have hCnk : ((Nat.choose n k : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.choose_ne_zero hkn
  have hneg := choose_neg_s s k
  have habs := absorb_s_eq s k hk1
  rw [hneg]
  field_simp
  linear_combination habs

private lemma residual_sum (s : ℂ) (n : ℕ) :
    ∑ k ∈ Finset.Icc 1 n, Ring.choose (-s) k / ((k : ℂ) * (Nat.choose n k : ℂ))
      = s * (∑ k ∈ Finset.Icc 1 n, (((-1 : ℂ) ^ k * Ring.choose (s + (k : ℂ) - 1) (k - 1)) / ((k :
        ℂ) ^ 2 * (Nat.choose n k : ℂ)))) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
  have hkn : k ≤ n := (Finset.mem_Icc.mp hk).2
  exact residual_term s n k hk1 hkn

/--
**Alternating binomial transform of the squared harmonic numbers.** For a complex number
$z$ and $k \in \mathbb{N}$ write $\binom{z}{k} = z(z-1)\cdots(z-k+1)/k!$ (the empty product
being $1$), and let $H_k = 1 + \frac{1}{2} + \cdots + \frac{1}{k}$ be the $k$-th harmonic number.
Let $s$ be a complex number that is not a negative integer, and let $n \ge 1$. Then

$$
\sum_{k=1}^{n} (-1)^k \binom{s+n}{k} H_k^2 =
(-1)^n \binom{s+n-1}{n} \left(H_n^2 + \frac{2 H_n}{s+n} + \frac{2}{(s+n)^2}\right) +
\frac{H_n}{s+n} - \frac{2}{(s+n)^2} -
\frac{s}{s+n} \sum_{k=1}^{n} \frac{(-1)^k \binom{s+k-1}{k-1}}{k^2 \binom{n}{k}}.
$$

Source: Necdet Batır, "Finite Binomial Sum Identities with Harmonic Numbers,"
Journal of Integer Sequences 24 (2021), Article 21.4.3, Theorem 7 (label
`Theorem7`), equation (2.12), lines 287–293,
https://cs.uwaterloo.ca/journals/JIS/VOL24/Batir2/batir13.tex

Proves `Wanted` entry `binomial_transform_sq_harmonic`.
-/
theorem binomial_transform_sq_harmonic (s : ℂ) (n : ℕ)
    (hs : ∀ m : ℕ, s ≠ -((m : ℂ) + 1)) (hn : 0 < n) :
  ∑ k ∈ Finset.Icc 1 n,
      ((-1 : ℂ) ^ k * ((descPochhammer ℂ k).eval (s + (n : ℂ)) / (k.factorial : ℂ)) *
        (harmonic k : ℂ) ^ 2) =
    (-1 : ℂ) ^ n * ((descPochhammer ℂ n).eval (s + (n : ℂ) - 1) / (n.factorial : ℂ)) *
        ((harmonic n : ℂ) ^ 2 + 2 * (harmonic n : ℂ) / (s + (n : ℂ)) +
          2 / (s + (n : ℂ)) ^ 2) +
      (harmonic n : ℂ) / (s + (n : ℂ)) - 2 / (s + (n : ℂ)) ^ 2 -
      s / (s + (n : ℂ)) *
        ∑ k ∈ Finset.Icc 1 n,
          (((-1 : ℂ) ^ k * ((descPochhammer ℂ (k - 1)).eval (s + (k : ℂ) - 1) /
            ((k - 1).factorial : ℂ))) / ((k : ℂ) ^ 2 * (Nat.choose n k : ℂ))) := by
  have hx : s + (n : ℂ) ≠ 0 := by
    intro hcon
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    apply hs m
    push_cast at hcon ⊢
    linear_combination hcon
  have h_gen := general_id (s + (n : ℂ)) hx n
  have h_nx : (n : ℂ) - (s + (n : ℂ)) = -s := by ring
  rw [h_nx] at h_gen
  have h_res := residual_sum s n
  rw [h_res] at h_gen
  have h_bridge_LHS : ∀ k ∈ Finset.Icc 1 n,
      (-1 : ℂ) ^ k * ((descPochhammer ℂ k).eval (s + (n : ℂ)) / (k.factorial : ℂ)) * (harmonic k :
        ℂ) ^ 2
        = (-1 : ℂ) ^ k * Ring.choose (s + (n : ℂ)) k * (((harmonic k : ℚ) : ℂ)) ^ 2 := by
    intro k hk
    rw [bridge]
  have h_bridge_RHS1 :
      (-1 : ℂ) ^ n * ((descPochhammer ℂ n).eval (s + (n : ℂ) - 1) / (n.factorial : ℂ)) *
          ((harmonic n : ℂ) ^ 2 + 2 * (harmonic n : ℂ) / (s + (n : ℂ)) + 2 / (s + (n : ℂ)) ^ 2)
        = (-1 : ℂ) ^ n * Ring.choose ((s + (n : ℂ)) - 1) n * (((((harmonic n : ℚ) : ℂ)) ^ 2 + 2 *
          ((harmonic n : ℚ) : ℂ) / (s + (n : ℂ)) + 2 / (s + (n : ℂ)) ^ 2)) := by
    rw [bridge]
  have h_bridge_res : ∀ k ∈ Finset.Icc 1 n,
      (((-1 : ℂ) ^ k * ((descPochhammer ℂ (k - 1)).eval (s + (k : ℂ) - 1) / ((k - 1).factorial :
        ℂ))) / ((k : ℂ) ^ 2 * (Nat.choose n k : ℂ)))
        = (((-1 : ℂ) ^ k * Ring.choose (s + (k : ℂ) - 1) (k - 1)) / ((k : ℂ) ^ 2 * (Nat.choose n k
          : ℂ))) := by
    intro k hk
    rw [bridge]
  rw [Finset.sum_congr rfl h_bridge_LHS]
  rw [h_bridge_RHS1]
  rw [Finset.sum_congr rfl h_bridge_res]
  have h_factor : (1 / (s + (n : ℂ))) * (s * (∑ k ∈ Finset.Icc 1 n, (((-1 : ℂ) ^ k * Ring.choose (s
    + (k : ℂ) - 1) (k - 1)) / ((k : ℂ) ^ 2 * (Nat.choose n k : ℂ)))))
      = s / (s + (n : ℂ)) * (∑ k ∈ Finset.Icc 1 n, (((-1 : ℂ) ^ k * Ring.choose (s + (k : ℂ) - 1)
        (k - 1)) / ((k : ℂ) ^ 2 * (Nat.choose n k : ℂ)))) := by
    ring
  rw [h_factor] at h_gen
  exact h_gen
end MetaMathlibExt
