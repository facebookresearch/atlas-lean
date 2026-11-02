/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.NumberTheory.BernoulliPolynomials
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

@[expose] public section

namespace MetaMathlibExt

open scoped BigOperators

section

private theorem bernoulli_eval₂_expand (m : ℕ) (t : ℂ) :
    (Polynomial.bernoulli m).eval₂ (algebraMap ℚ ℂ) t =
      ∑ j ∈ Finset.range (m + 1), (bernoulli (m - j) : ℂ) * ((m.choose j : ℕ) : ℂ) * t ^ j := by
  rw [Polynomial.eval₂_eq_sum, Polynomial.sum_def]
  have hterm : ∀ j ∈ Finset.range (m + 1),
      (algebraMap ℚ ℂ) ((Polynomial.bernoulli m).coeff j) * t ^ j
      = (bernoulli (m - j) : ℂ) * ((m.choose j : ℕ) : ℂ) * t ^ j := by
    intro j hj
    have hjle : j ≤ m := by simp only [Finset.mem_range] at hj; omega
    simp only [Polynomial.coeff_bernoulli, hjle, ↓reduceIte]
    simp [map_mul, map_natCast]
  have hsub : (Polynomial.bernoulli m).support ⊆ Finset.range (m + 1) := by
    intro x hx
    simp only [Finset.mem_range]
    rw [Polynomial.mem_support_iff] at hx
    by_contra hle
    push Not at hle
    apply hx
    simp only [Polynomial.coeff_bernoulli]
    split_ifs with h
    · exact absurd h (by omega)
    · rfl
  have hvan : ∀ x ∈ Finset.range (m + 1), x ∉ (Polynomial.bernoulli m).support →
      (algebraMap ℚ ℂ) ((Polynomial.bernoulli m).coeff x) * t ^ x = 0 := by
    intro x _ hxns
    rw [Polynomial.mem_support_iff] at hxns
    push Not at hxns
    have hcoeff : (Polynomial.bernoulli m).coeff x = 0 := hxns
    simp [hcoeff]
  calc ∑ n ∈ (Polynomial.bernoulli m).support,
          (algebraMap ℚ ℂ) ((Polynomial.bernoulli m).coeff n) * t ^ n
      = ∑ n ∈ Finset.range (m + 1),
          (algebraMap ℚ ℂ) ((Polynomial.bernoulli m).coeff n) * t ^ n :=
        Finset.sum_subset hsub hvan
    _ = _ := Finset.sum_congr rfl hterm

private theorem zpow_mul_pow_eq (a : ℂ) (ha : a ≠ 0) (n i j k : ℕ)
    (hi : i ≤ n) (hk : k = i + 1 - j) (hj : 1 ≤ j) (hji : j ≤ i + 1) :
    a ^ ((n : ℤ) - 1 - (i : ℤ)) * a ^ j = a ^ (n - k) := by
  have hsum : k + j = i + 1 := by rw [hk]; exact Nat.sub_add_cancel hji
  have hkn : k ≤ n := by omega
  have e1 : ((i + 1 - j : ℕ) : ℤ) = (i : ℤ) + 1 - (j : ℤ) := by
    rw [Nat.cast_sub hji, Nat.cast_add, Nat.cast_one]
  have e2 : ((n - k : ℕ) : ℤ) = (n : ℤ) - (k : ℤ) := Nat.cast_sub hkn
  have ek : ((k : ℕ) : ℤ) = ((i + 1 - j : ℕ) : ℤ) := by rw [hk]
  have hexp : (n : ℤ) - 1 - (i : ℤ) + ((j : ℕ) : ℤ) = ((n - k : ℕ) : ℤ) := by
    rw [e2, ek, e1]; ring
  rw [← zpow_natCast a j, ← zpow_add₀ ha, hexp]
  exact (zpow_natCast a (n - k)).symm

private theorem key_expand (a : ℂ) (ha : a ≠ 0) (n i : ℕ) (hi : i ≤ n) :
    a ^ ((n : ℤ) - 1 - (i : ℤ)) *
      ((Polynomial.bernoulli (i + 1)).eval₂ (algebraMap ℚ ℂ) a - (bernoulli (i + 1) : ℂ))
      = ∑ k ∈ Finset.range (i + 1),
        (((i + 1).choose k : ℕ) : ℂ) * (bernoulli k : ℂ) * a ^ (n - k) := by
  rw [bernoulli_eval₂_expand (i + 1) a, Finset.sum_range_succ']
  have hF0 : (bernoulli (i + 1 - 0) : ℂ) * ((((i + 1).choose 0 : ℕ)) : ℂ) * a ^ (0 : ℕ)
      = (bernoulli (i + 1) : ℂ) := by simp
  rw [hF0, add_sub_cancel_right, Finset.mul_sum]
  have hR := Finset.sum_range_reflect
    (fun k => (((i + 1).choose k : ℕ) : ℂ) * (bernoulli k : ℂ) * a ^ (n - k)) (i + 1)
  rw [← hR]
  apply Finset.sum_congr rfl
  intro j hj
  have hji : j ≤ i := by simp only [Finset.mem_range] at hj; omega
  have hm : (i + 1) - 1 - j = i - j := by omega
  rw [hm]
  have hc1 : i + 1 - (j + 1) = i - j := by omega
  have hcc : ((((i + 1).choose (i - j) : ℕ)) : ℂ) = ((((i + 1).choose (j + 1) : ℕ)) : ℂ) := by
    rw [← hc1, Nat.choose_symm (show j + 1 ≤ i + 1 by omega)]
  have hz : a ^ ((n : ℤ) - 1 - (i : ℤ)) * a ^ (j + 1) = a ^ (n - (i - j)) :=
    zpow_mul_pow_eq a ha n i (j + 1) (i - j) hi hc1.symm (by omega) (by omega)
  rw [hc1]
  have hmove : a ^ ((n : ℤ) - 1 - (i : ℤ)) *
      ((bernoulli (i - j) : ℂ) * ((((i + 1).choose (j + 1) : ℕ)) : ℂ) * a ^ (j + 1))
      = (bernoulli (i - j) : ℂ) * ((((i + 1).choose (j + 1) : ℕ)) : ℂ) *
        (a ^ ((n : ℤ) - 1 - (i : ℤ)) * a ^ (j + 1)) := by ring
  rw [hmove, hz, ← hcc]
  ring


private theorem choose_div_key (n i : ℕ) (hi : i ≤ n) :
    ((((n.choose i : ℕ))) : ℂ) * ((n : ℂ) + 1)
      = ((((n + 1).choose (i + 1) : ℕ)) : ℂ) * ((i : ℂ) + 1) := by
  have hi1 : i + 1 ≤ n + 1 := Nat.succ_le_succ hi
  have hni : n + 1 - (i + 1) = n - i := Nat.succ_sub_succ n i
  have e1 : ((((n.choose i : ℕ))) : ℂ) * (((Nat.factorial i : ℂ)) : ℂ) *
      (((Nat.factorial (n - i) : ℂ)) : ℂ) = (((Nat.factorial n : ℂ)) : ℂ) :=
    by exact_mod_cast Nat.choose_mul_factorial_mul_factorial hi
  have e2 : ((((n + 1).choose (i + 1) : ℕ)) : ℂ) * (((Nat.factorial (i + 1) : ℂ)) : ℂ) *
      (((Nat.factorial (n - i) : ℂ)) : ℂ) = (((Nat.factorial (n + 1) : ℂ)) : ℂ) := by
    have h := Nat.choose_mul_factorial_mul_factorial hi1
    rw [hni] at h
    exact_mod_cast h
  have fI : (((Nat.factorial (i + 1) : ℂ)) : ℂ) =
      ((i : ℂ) + 1) * (((Nat.factorial i : ℂ)) : ℂ) := by
    rw [Nat.factorial_succ]; push_cast; ring
  have fN : (((Nat.factorial (n + 1) : ℂ)) : ℂ) =
      ((n : ℂ) + 1) * (((Nat.factorial n : ℂ)) : ℂ) := by
    rw [Nat.factorial_succ]; push_cast; ring
  have key1 : ((((n.choose i : ℕ))) : ℂ) * ((n : ℂ) + 1) *
      (((((Nat.factorial i : ℂ)) : ℂ) * (((Nat.factorial (n - i) : ℂ)) : ℂ)))
      = (((Nat.factorial (n + 1) : ℂ)) : ℂ) := by
    linear_combination ((n : ℂ) + 1) * e1 - fN
  have key2 : ((((n + 1).choose (i + 1) : ℕ)) : ℂ) * ((i : ℂ) + 1) *
      (((((Nat.factorial i : ℂ)) : ℂ) * (((Nat.factorial (n - i) : ℂ)) : ℂ)))
      = (((Nat.factorial (n + 1) : ℂ)) : ℂ) := by
    linear_combination e2 - ((((n + 1).choose (i + 1) : ℕ)) : ℂ) *
      (((Nat.factorial (n - i) : ℂ)) : ℂ) * fI
  have hF : (((((Nat.factorial i : ℂ)) : ℂ) * (((Nat.factorial (n - i) : ℂ)) : ℂ))) ≠ 0 := by
    apply mul_ne_zero <;> exact_mod_cast Nat.factorial_ne_zero _
  have key : ((((n.choose i : ℕ))) : ℂ) * ((n : ℂ) + 1)
      = ((((n + 1).choose (i + 1) : ℕ)) : ℂ) * ((i : ℂ) + 1) :=
    mul_right_cancel₀ hF (by rw [key1, key2])
  exact key

private theorem choose_T_symm (n k l : ℕ) (h : k + l ≤ n) :
    ((((n + 1).choose k : ℕ)) : ℂ) * ((((n + 1 - k).choose l : ℕ)) : ℂ)
      = ((((n + 1).choose l : ℕ)) : ℂ) * ((((n + 1 - l).choose k : ℕ)) : ℂ) := by
  have h1 : k ≤ n + 1 := by omega
  have h2 : l ≤ n + 1 - k := by omega
  have h3 : l ≤ n + 1 := by omega
  have h4 : k ≤ n + 1 - l := by omega
  have hM : n + 1 - k - l = n + 1 - l - k := by omega
  have e1 : ((((n + 1).choose k : ℕ)) : ℂ) * ((Nat.factorial k : ℂ)) *
      ((Nat.factorial (n + 1 - k) : ℂ)) = ((Nat.factorial (n + 1) : ℂ)) :=
    by exact_mod_cast Nat.choose_mul_factorial_mul_factorial h1
  have e2 : ((((n + 1 - k).choose l : ℕ)) : ℂ) * ((Nat.factorial l : ℂ)) *
      ((Nat.factorial (n + 1 - k - l) : ℂ)) = ((Nat.factorial (n + 1 - k) : ℂ)) :=
    by exact_mod_cast Nat.choose_mul_factorial_mul_factorial h2
  have e3 : ((((n + 1).choose l : ℕ)) : ℂ) * ((Nat.factorial l : ℂ)) *
      ((Nat.factorial (n + 1 - l) : ℂ)) = ((Nat.factorial (n + 1) : ℂ)) :=
    by exact_mod_cast Nat.choose_mul_factorial_mul_factorial h3
  have e4 : ((((n + 1 - l).choose k : ℕ)) : ℂ) * ((Nat.factorial k : ℂ)) *
      ((Nat.factorial (n + 1 - l - k) : ℂ)) = ((Nat.factorial (n + 1 - l) : ℂ)) :=
    by exact_mod_cast Nat.choose_mul_factorial_mul_factorial h4
  have key1 : ((((n + 1).choose k : ℕ)) : ℂ) * ((((n + 1 - k).choose l : ℕ)) : ℂ) *
      ((Nat.factorial k : ℂ) * ((Nat.factorial l : ℂ) *
        ((Nat.factorial (n + 1 - k - l) : ℂ))))
      = ((Nat.factorial (n + 1) : ℂ)) := by
    linear_combination e1 + ((((n + 1).choose k : ℕ)) : ℂ) * ((Nat.factorial k : ℂ)) * e2
  have key2 : ((((n + 1).choose l : ℕ)) : ℂ) * ((((n + 1 - l).choose k : ℕ)) : ℂ) *
      ((Nat.factorial k : ℂ) * ((Nat.factorial l : ℂ) *
        ((Nat.factorial (n + 1 - l - k) : ℂ))))
      = ((Nat.factorial (n + 1) : ℂ)) := by
    linear_combination e3 + ((((n + 1).choose l : ℕ)) : ℂ) * ((Nat.factorial l : ℂ)) * e4
  rw [← hM] at key2
  have hK : ((Nat.factorial k : ℂ)) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  have hL : ((Nat.factorial l : ℂ)) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero l
  have hM0 : ((Nat.factorial (n + 1 - k - l) : ℂ)) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero _
  have hZ : ((Nat.factorial k : ℂ) * ((Nat.factorial l : ℂ) *
      ((Nat.factorial (n + 1 - k - l) : ℂ)))) ≠ 0 :=
    mul_ne_zero hK (mul_ne_zero hL hM0)
  exact mul_right_cancel₀ hZ (by rw [key1, key2])

private theorem succ_cast_ne_zero (i : ℕ) : ((i : ℂ) + 1) ≠ 0 := by
  have hc : ((i : ℂ) + 1) = ((i + 1 : ℕ) : ℂ) := by push_cast; ring
  rw [hc]
  exact_mod_cast Nat.succ_ne_zero i

private theorem T1_helper (n i k : ℕ) (hki : k ≤ i) (hin : i ≤ n) :
    ((((n + 1).choose (i + 1) : ℕ)) : ℂ) * ((((i + 1).choose k : ℕ)) : ℂ)
      = ((((n + 1).choose k : ℕ)) : ℂ) * ((((n + 1 - k).choose (n - i) : ℕ)) : ℂ) := by
  have eA : (n + 1).choose (i + 1) = (n + 1).choose (n - i) := by
    rw [← Nat.choose_symm (show i + 1 ≤ n + 1 by omega)]
    congr 1
    omega
  have eB : n + 1 - (n - i) = i + 1 := by
    have h1 : (i + 1) + (n - i) = n + 1 := by
      have h0 : (n - i) + i = n := Nat.sub_add_cancel hin
      omega
    rw [← h1, Nat.add_sub_cancel]
  have eAc : ((((n + 1).choose (i + 1) : ℕ)) : ℂ) = ((((n + 1).choose (n - i) : ℕ)) : ℂ) := by
    exact_mod_cast eA
  have hT := choose_T_symm n (n - i) k (by
    have h0 : (n - i) + i = n := Nat.sub_add_cancel hin
    omega)
  rw [eB] at hT
  rw [eAc]
  exact hT

private theorem sigma_at (r : ℂ) (i : ℕ)
    (sigma : ℂ → ℕ → ℂ)
    (hsigma : ∀ x j, (((j + 1 : ℕ)) : ℂ) * sigma x j =
      (Polynomial.bernoulli (j + 1)).eval₂ (algebraMap ℚ ℂ) (x + 1) - (bernoulli (j + 1) : ℂ)) :
    sigma (r - 1) i =
      ((Polynomial.bernoulli (i + 1)).eval₂ (algebraMap ℚ ℂ) r - (bernoulli (i + 1) : ℂ)) /
        ((i : ℂ) + 1) := by
  have h := hsigma (r - 1) i
  have hr1 : (r - 1) + 1 = r := sub_add_cancel r 1
  rw [hr1] at h
  have hcast : ((((i + 1 : ℕ))) : ℂ) = (i : ℂ) + 1 := by push_cast; ring
  rw [hcast] at h
  have hI1 := succ_cast_ne_zero i
  rw [eq_div_iff hI1]
  linear_combination h

private theorem per_side (r q : ℂ) (hr : r ≠ 0) (n i : ℕ) (hi : i ≤ n)
    (sigma : ℂ → ℕ → ℂ)
    (hsigma : ∀ x j, (((j + 1 : ℕ)) : ℂ) * sigma x j =
      (Polynomial.bernoulli (j + 1)).eval₂ (algebraMap ℚ ℂ) (x + 1) - (bernoulli (j + 1) : ℂ)) :
    ((n : ℂ) + 1) * ((n.choose i : ℂ) * (bernoulli (n - i) : ℂ) *
      (r ^ ((n : ℤ) - 1 - (i : ℤ)) * q ^ i * sigma (r - 1) i))
      = ∑ k ∈ Finset.range (i + 1),
        (((n + 1).choose k : ℂ) * ((((n + 1 - k).choose (n - i) : ℕ)) : ℂ)) *
        (bernoulli (n - i) : ℂ) * (bernoulli k : ℂ) * r ^ (n - k) * q ^ i := by
  have hs := sigma_at r i sigma hsigma
  have hkey := key_expand r hr n i hi
  have hdiv := choose_div_key n i hi
  have hI1 := succ_cast_ne_zero i
  have hT : ∀ k ∈ Finset.range (i + 1),
      ((((n + 1).choose (i + 1) : ℕ)) : ℂ) * ((((i + 1).choose k : ℕ)) : ℂ)
        = ((((n + 1).choose k : ℕ)) : ℂ) * ((((n + 1 - k).choose (n - i) : ℕ)) : ℂ) := by
    intro k hk
    have hki : k ≤ i := by simp only [Finset.mem_range] at hk; omega
    exact T1_helper n i k hki hi
  have regroup : r ^ ((n : ℤ) - 1 - (i : ℤ)) * q ^ i *
      (((Polynomial.bernoulli (i + 1)).eval₂ (algebraMap ℚ ℂ) r - (bernoulli (i + 1) : ℂ)) /
        ((i : ℂ) + 1))
      = q ^ i * (r ^ ((n : ℤ) - 1 - (i : ℤ)) *
        ((Polynomial.bernoulli (i + 1)).eval₂ (algebraMap ℚ ℂ) r - (bernoulli (i + 1) : ℂ))) /
        ((i : ℂ) + 1) := by ring
  rw [hs, regroup, hkey]
  have hmid : ((n : ℂ) + 1) * ((n.choose i : ℂ) * (bernoulli (n - i) : ℂ) *
      (q ^ i * (∑ k ∈ Finset.range (i + 1),
        ((((i + 1).choose k : ℕ)) : ℂ) * (bernoulli k : ℂ) * r ^ (n - k)) / ((i : ℂ) + 1)))
      = ((((n + 1).choose (i + 1) : ℕ)) : ℂ) * (bernoulli (n - i) : ℂ) * q ^ i *
        (∑ k ∈ Finset.range (i + 1),
          ((((i + 1).choose k : ℕ)) : ℂ) * (bernoulli k : ℂ) * r ^ (n - k)) := by
    field_simp
    linear_combination ((bernoulli (n - i) : ℂ) * q ^ i *
      (∑ k ∈ Finset.range (i + 1),
        ((((i + 1).choose k : ℕ)) : ℂ) * (bernoulli k : ℂ) * r ^ (n - k))) * hdiv
  rw [hmid, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hkT := hT k hk
  linear_combination ((bernoulli (n - i) : ℂ) * (bernoulli k : ℂ) * (r ^ (n - k)) * (q ^ i)) * hkT

private theorem double_sum_eq (a b : ℂ) (ha : a ≠ 0) (hb : b ≠ 0) (n : ℕ)
    (sigma : ℂ → ℕ → ℂ)
    (hsigma : ∀ x j, (((j + 1 : ℕ)) : ℂ) * sigma x j =
      (Polynomial.bernoulli (j + 1)).eval₂ (algebraMap ℚ ℂ) (x + 1) - (bernoulli (j + 1) : ℂ)) :
    (∑ i ∈ Finset.range (n + 1), (n.choose i : ℂ) * (bernoulli (n - i) : ℂ) *
      (a ^ ((n : ℤ) - 1 - (i : ℤ)) * b ^ i * sigma (a - 1) i))
    = (∑ i ∈ Finset.range (n + 1), (n.choose i : ℂ) * (bernoulli (n - i) : ℂ) *
      (a ^ i * b ^ ((n : ℤ) - 1 - (i : ℤ)) * sigma (b - 1) i)) := by
  have hN1 := succ_cast_ne_zero n
  apply mul_left_cancel₀ hN1
  rw [Finset.mul_sum, Finset.mul_sum]
  have eA : (∑ i ∈ Finset.range (n + 1), ((n : ℂ) + 1) * ((n.choose i : ℂ) *
      (bernoulli (n - i) : ℂ) * (a ^ ((n : ℤ) - 1 - (i : ℤ)) * b ^ i * sigma (a - 1) i)))
      = ∑ x ∈ (Finset.range (n + 1)).sigma (fun i => Finset.range (i + 1)),
        (((n + 1).choose x.2 : ℂ) * ((((n + 1 - x.2).choose (n - x.1) : ℕ)) : ℂ)) *
        (bernoulli (n - x.1) : ℂ) * (bernoulli x.2 : ℂ) * a ^ (n - x.2) * b ^ x.1 := by
    have h1 : (∑ i ∈ Finset.range (n + 1), ((n : ℂ) + 1) * ((n.choose i : ℂ) *
        (bernoulli (n - i) : ℂ) * (a ^ ((n : ℤ) - 1 - (i : ℤ)) * b ^ i * sigma (a - 1) i)))
        = ∑ i ∈ Finset.range (n + 1), ∑ k ∈ Finset.range (i + 1),
          (((n + 1).choose k : ℂ) * ((((n + 1 - k).choose (n - i) : ℕ)) : ℂ)) *
          (bernoulli (n - i) : ℂ) * (bernoulli k : ℂ) * a ^ (n - k) * b ^ i :=
      Finset.sum_congr rfl (fun i hi =>
        per_side a b ha n i (Nat.le_of_lt_succ (Finset.mem_range.mp hi)) sigma hsigma)
    rw [h1]
    exact Finset.sum_sigma' _ _ _
  have eB : (∑ i ∈ Finset.range (n + 1), ((n : ℂ) + 1) * ((n.choose i : ℂ) *
      (bernoulli (n - i) : ℂ) * (a ^ i * b ^ ((n : ℤ) - 1 - (i : ℤ)) * sigma (b - 1) i)))
      = ∑ x ∈ (Finset.range (n + 1)).sigma (fun i => Finset.range (i + 1)),
        (((n + 1).choose x.2 : ℂ) * ((((n + 1 - x.2).choose (n - x.1) : ℕ)) : ℂ)) *
        (bernoulli (n - x.1) : ℂ) * (bernoulli x.2 : ℂ) * b ^ (n - x.2) * a ^ x.1 := by
    have h1 : (∑ i ∈ Finset.range (n + 1), ((n : ℂ) + 1) * ((n.choose i : ℂ) *
        (bernoulli (n - i) : ℂ) * (a ^ i * b ^ ((n : ℤ) - 1 - (i : ℤ)) * sigma (b - 1) i)))
        = ∑ i ∈ Finset.range (n + 1), ∑ k ∈ Finset.range (i + 1),
          (((n + 1).choose k : ℂ) * ((((n + 1 - k).choose (n - i) : ℕ)) : ℂ)) *
          (bernoulli (n - i) : ℂ) * (bernoulli k : ℂ) * b ^ (n - k) * a ^ i :=
      Finset.sum_congr rfl (fun i hi => by
        have h := per_side b a hb n i
          (Nat.le_of_lt_succ (Finset.mem_range.mp hi)) sigma hsigma
        rwa [mul_comm (a ^ i) (b ^ ((n : ℤ) - 1 - (i : ℤ)))] )
    rw [h1]
    exact Finset.sum_sigma' _ _ _
  rw [eA, eB]
  have hmem : ∀ p (_ : p ∈ (Finset.range (n + 1)).sigma (fun i => Finset.range (i + 1))),
      ⟨n - p.2, n - p.1⟩ ∈ (Finset.range (n + 1)).sigma (fun i => Finset.range (i + 1)) := by
    intro p hp
    rw [Finset.mem_sigma] at hp ⊢
    obtain ⟨h1, h2⟩ := hp
    simp only [Finset.mem_range] at h1 h2 ⊢
    have hle : p.2 ≤ p.1 := by omega
    exact ⟨Nat.lt_succ_of_le (Nat.sub_le _ _),
      Nat.lt_succ_of_le (Nat.sub_le_sub_left hle n)⟩
  have hround : ∀ p (_ : p ∈ (Finset.range (n + 1)).sigma (fun i => Finset.range (i + 1))),
      ⟨n - (n - p.1), n - (n - p.2)⟩ = p := by
    intro p hp
    rw [Finset.mem_sigma] at hp
    obtain ⟨h1, h2⟩ := hp
    simp only [Finset.mem_range] at h1 h2
    have hi1 : p.1 ≤ n := by omega
    have hk1 : p.2 ≤ n := by omega
    rw [Nat.sub_sub_self hi1, Nat.sub_sub_self hk1]
  have hterm : ∀ p (_ : p ∈ (Finset.range (n + 1)).sigma (fun i => Finset.range (i + 1))),
      (((n + 1).choose p.2 : ℂ) * ((((n + 1 - p.2).choose (n - p.1) : ℕ)) : ℂ)) *
        (bernoulli (n - p.1) : ℂ) * (bernoulli p.2 : ℂ) * a ^ (n - p.2) * b ^ p.1
      = (((n + 1).choose (n - p.1) : ℂ) *
          ((((n + 1 - (n - p.1)).choose (n - (n - p.2)) : ℕ)) : ℂ)) *
        (bernoulli (n - (n - p.2)) : ℂ) * (bernoulli (n - p.1) : ℂ) *
        b ^ (n - (n - p.1)) * a ^ (n - p.2) := by
    intro p hp
    rw [Finset.mem_sigma] at hp
    obtain ⟨h1, h2⟩ := hp
    simp only [Finset.mem_range] at h1 h2
    have hi1 : p.1 ≤ n := by omega
    have hki : p.2 ≤ p.1 := by omega
    have hk1 : p.2 ≤ n := le_trans hki hi1
    have e_ik : n - (n - p.1) = p.1 := Nat.sub_sub_self hi1
    have e_ki : n - (n - p.2) = p.2 := Nat.sub_sub_self hk1
    have hkle : (n - p.1) + p.2 ≤ n := by
      have h0 : (n - p.1) + p.1 = n := Nat.sub_add_cancel hi1
      omega
    have hT := choose_T_symm n (n - p.1) p.2 hkle
    rw [e_ki, e_ik]
    linear_combination (-((bernoulli (n - p.1) : ℂ) * (bernoulli p.2 : ℂ) *
      (a ^ (n - p.2)) * (b ^ p.1))) * hT
  exact Finset.sum_bij' (s := (Finset.range (n + 1)).sigma (fun i => Finset.range (i + 1)))
    (t := (Finset.range (n + 1)).sigma (fun i => Finset.range (i + 1)))
    (fun p _ => ⟨n - p.2, n - p.1⟩) (fun p _ => ⟨n - p.2, n - p.1⟩)
    hmem hmem hround hround hterm

private theorem sigma_zero (x : ℂ)
    (sigma : ℂ → ℕ → ℂ)
    (hsigma : ∀ x j, (((j + 1 : ℕ)) : ℂ) * sigma x j =
      (Polynomial.bernoulli (j + 1)).eval₂ (algebraMap ℚ ℂ) (x + 1) - (bernoulli (j + 1) : ℂ)) :
    sigma x 0 = x + 1 := by
  have h := hsigma x 0
  simp only [zero_add, Nat.cast_one, one_mul] at h
  have hE : (Polynomial.bernoulli 1).eval₂ (algebraMap ℚ ℂ) (x + 1) = (x + 1) - 1 / 2 := by
    rw [Polynomial.bernoulli_one, Polynomial.eval₂_sub, Polynomial.eval₂_X, Polynomial.eval₂_C]
    simp [map_inv₀]
  have hB : ((bernoulli 1 : ℚ) : ℂ) = -1 / 2 := by
    rw [bernoulli_one]; norm_num
  rw [hE, hB] at h
  rw [h]; ring

/-- **Tuenter's power-sum identity for Bernoulli numbers.** Let $a$ and $b$ be nonzero complex
numbers and let $n \ge 1$ be a natural number with $b^n \ne a^n$. Let $\sigma_x(i) \in \mathbb{C}$,
for $x \in \mathbb{C}$ and $i \in \mathbb{N}$, satisfy
$(i+1)\,\sigma_x(i) = B_{i+1}(x+1) - B_{i+1}$ for all $x$ and $i$, where $B_m(t)$ denotes the
Bernoulli polynomial and $B_m$ the Bernoulli number, with $B_1 = -\tfrac{1}{2}$. Then

$$B_n = \frac{1}{b^n - a^n} \sum_{i=1}^{n} \binom{n}{i} B_{n-i}
\left( a^{n-1-i} \, b^i \, \sigma_{a-1}(i) - a^i \, b^{n-1-i} \, \sigma_{b-1}(i) \right),$$

where the exponents $n - 1 - i$ are integers, equal to $-1$ when $i = n$.

For a natural number $x$ and $i \ge 1$ the relation gives $\sigma_x(i) = 1^i + 2^i + \dots + x^i$.

Proves `Wanted` entry `tuenter_bernoulli_power_sum_identity`.

Source: Jitender Singh, *On an Arithmetic Convolution*, Journal of Integer
Sequences 17 (2014), Article 14.6.7, Corollary with equation `eq23`,
lines 339–344, identified there as Tuenter's identity at `c = 0`, line 348,
<https://cs.uwaterloo.ca/journals/JIS/VOL17/Singh/singh8.tex>.
-/
theorem tuenter_bernoulli_power_sum_identity
    (a b : ℂ) (n : ℕ) (hn : 0 < n)
    (ha : a ≠ 0) (hb : b ≠ 0)
    (sigma : ℂ → ℕ → ℂ)
    (hsigma : ∀ x i,
      ((i + 1 : ℕ) : ℂ) * sigma x i =
        (Polynomial.bernoulli (i + 1)).eval₂ (algebraMap ℚ ℂ) (x + 1) -
          (bernoulli (i + 1) : ℂ))
    (hden : b ^ n - a ^ n ≠ 0) :
    (bernoulli n : ℂ) =
      1 / (b ^ n - a ^ n) *
        ∑ i ∈ Finset.Icc 1 n,
          (n.choose i : ℂ) * (bernoulli (n - i) : ℂ) *
            (a ^ ((n : ℤ) - 1 - (i : ℤ)) * b ^ i * sigma (a - 1) i -
              a ^ i * b ^ ((n : ℤ) - 1 - (i : ℤ)) * sigma (b - 1) i) := by
  rw [div_mul_eq_mul_div, one_mul, eq_div_iff hden]
  have hIcc : Finset.Icc 1 n = (Finset.range (n + 1)).erase 0 := by
    ext x
    simp only [Finset.mem_Icc, Finset.mem_erase, Finset.mem_range]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨by omega, by omega⟩
    · rintro ⟨h1, h2⟩
      exact ⟨by omega, by omega⟩
  have h0mem : 0 ∈ Finset.range (n + 1) := Finset.mem_range.mpr (Nat.succ_pos n)
  have hrange : (∑ i ∈ Finset.range (n + 1),
      (n.choose i : ℂ) * (bernoulli (n - i) : ℂ) *
        (a ^ ((n : ℤ) - 1 - (i : ℤ)) * b ^ i * sigma (a - 1) i -
          a ^ i * b ^ ((n : ℤ) - 1 - (i : ℤ)) * sigma (b - 1) i)) = 0 := by
    have hsub : (∑ i ∈ Finset.range (n + 1),
        (n.choose i : ℂ) * (bernoulli (n - i) : ℂ) *
          (a ^ ((n : ℤ) - 1 - (i : ℤ)) * b ^ i * sigma (a - 1) i -
            a ^ i * b ^ ((n : ℤ) - 1 - (i : ℤ)) * sigma (b - 1) i))
        = (∑ i ∈ Finset.range (n + 1), (n.choose i : ℂ) * (bernoulli (n - i) : ℂ) *
            (a ^ ((n : ℤ) - 1 - (i : ℤ)) * b ^ i * sigma (a - 1) i))
          - (∑ i ∈ Finset.range (n + 1), (n.choose i : ℂ) * (bernoulli (n - i) : ℂ) *
            (a ^ i * b ^ ((n : ℤ) - 1 - (i : ℤ)) * sigma (b - 1) i)) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [hsub, double_sum_eq a b ha hb n sigma hsigma, sub_self]
  have hF0 : (n.choose 0 : ℂ) * (bernoulli (n - 0) : ℂ) *
      (a ^ ((n : ℤ) - 1 - (((0 : ℕ)) : ℤ)) * b ^ (0 : ℕ) * sigma (a - 1) 0 -
        a ^ (0 : ℕ) * b ^ ((n : ℤ) - 1 - (((0 : ℕ)) : ℤ)) * sigma (b - 1) 0)
      = (a ^ n - b ^ n) * (bernoulli n : ℂ) := by
    have s1 := sigma_zero (a - 1) sigma hsigma
    have s2 := sigma_zero (b - 1) sigma hsigma
    have ha1 : (a - 1) + 1 = a := sub_add_cancel a 1
    have hb1 : (b - 1) + 1 = b := sub_add_cancel b 1
    rw [s1, s2, ha1, hb1]
    have hz : ((n : ℤ) - 1 - ((((0 : ℕ))) : ℤ)) = ((((n - 1 : ℕ))) : ℤ) := by
      rw [Nat.cast_zero, sub_zero, ← Nat.cast_one]
      exact (Nat.cast_sub (by omega : 1 ≤ n)).symm
    rw [hz, zpow_natCast, zpow_natCast, Nat.choose_zero_right, Nat.sub_zero]
    simp only [pow_zero, one_mul, mul_one]
    have ea : a ^ (n - 1) * a = a ^ n := by
      rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ n)]
    have eb : b ^ (n - 1) * b = b ^ n := by
      rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ n)]
    rw [ea, eb]
    ring
  have hsplit : (n.choose 0 : ℂ) * (bernoulli (n - 0) : ℂ) *
      (a ^ ((n : ℤ) - 1 - (((0 : ℕ)) : ℤ)) * b ^ (0 : ℕ) * sigma (a - 1) 0 -
        a ^ (0 : ℕ) * b ^ ((n : ℤ) - 1 - (((0 : ℕ)) : ℤ)) * sigma (b - 1) 0)
      + (∑ i ∈ Finset.Icc 1 n,
        (n.choose i : ℂ) * (bernoulli (n - i) : ℂ) *
          (a ^ ((n : ℤ) - 1 - (i : ℤ)) * b ^ i * sigma (a - 1) i -
            a ^ i * b ^ ((n : ℤ) - 1 - (i : ℤ)) * sigma (b - 1) i))
      = (∑ i ∈ Finset.range (n + 1),
        (n.choose i : ℂ) * (bernoulli (n - i) : ℂ) *
          (a ^ ((n : ℤ) - 1 - (i : ℤ)) * b ^ i * sigma (a - 1) i -
            a ^ i * b ^ ((n : ℤ) - 1 - (i : ℤ)) * sigma (b - 1) i)) := by
    rw [hIcc]
    exact (Finset.add_sum_erase (Finset.range (n + 1))
      (fun i => (n.choose i : ℂ) * (bernoulli (n - i) : ℂ) *
        (a ^ ((n : ℤ) - 1 - (i : ℤ)) * b ^ i * sigma (a - 1) i -
          a ^ i * b ^ ((n : ℤ) - 1 - (i : ℤ)) * sigma (b - 1) i)) h0mem)
  rw [hrange] at hsplit
  linear_combination hF0 - hsplit

end

end MetaMathlibExt
