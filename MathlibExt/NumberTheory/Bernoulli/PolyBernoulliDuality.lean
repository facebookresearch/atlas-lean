/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.Enumerative.Stirling
public import Mathlib.Data.Rat.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

open scoped BigOperators

private noncomputable def Hsum (n s : ℕ) : ℚ :=
  ∑ r ∈ Finset.range (n + 1),
    (-1 : ℚ) ^ r * (Nat.factorial r : ℚ) * (Nat.stirlingSecond n r : ℚ) *
      (((r + 1).descFactorial s : ℕ) : ℚ)

private lemma descFactorial_pascal_Q (x s : ℕ) :
    (((x + 1).descFactorial (s + 1) : ℕ) : ℚ) =
    (((x.descFactorial (s + 1) : ℕ)) : ℚ) + ((s + 1 : ℕ) : ℚ) * ((((x.descFactorial s : ℕ))) : ℚ) := by
  have h := Nat.descFactorial_eq_factorial_mul_choose (x + 1) (s + 1)
  have h1 := Nat.descFactorial_eq_factorial_mul_choose x (s + 1)
  have h2 := Nat.descFactorial_eq_factorial_mul_choose x s
  have hc : (x + 1).choose (s + 1) = x.choose s + x.choose (s + 1) := Nat.choose_succ_succ x s
  have hf : ((s + 1).factorial : ℚ) = ((s + 1 : ℕ) : ℚ) * ((s.factorial : ℕ) : ℚ) := by
    exact_mod_cast Nat.factorial_succ s
  have e1 : ((((x + 1).descFactorial (s + 1) : ℕ)) : ℚ) =
      (((s + 1).factorial : ℕ) : ℚ) * ((((x + 1).choose (s + 1) : ℕ)) : ℚ) := by
    exact_mod_cast congrArg Nat.cast h
  have e2 : ((((x.descFactorial (s + 1) : ℕ))) : ℚ) =
      (((s + 1).factorial : ℕ) : ℚ) * ((((x.choose (s + 1) : ℕ))) : ℚ) := by
    exact_mod_cast congrArg Nat.cast h1
  have e3 : ((((x.descFactorial s : ℕ))) : ℚ) =
      (((s.factorial : ℕ)) : ℚ) * ((((x.choose s : ℕ))) : ℚ) := by
    exact_mod_cast congrArg Nat.cast h2
  rw [e1, e2, e3, hc]
  push_cast
  rw [hf]
  push_cast
  ring

private lemma mul_descFactorial_eq (t s : ℕ) :
    (((t + 1 : ℕ)) : ℚ) * ((((t + 1).descFactorial s : ℕ)) : ℚ) =
    ((((t + 1).descFactorial (s + 1) : ℕ)) : ℚ) + (((s : ℕ)) : ℚ) * ((((t + 1).descFactorial s : ℕ)) : ℚ) := by
  by_cases hle : s ≤ t + 1
  · have hdf := Nat.descFactorial_succ (t + 1) s
    have hsub : ((((t + 1 - s : ℕ)))) = (((t + 1 : ℕ)) : ℚ) - (((s : ℕ)) : ℚ) := Nat.cast_sub hle
    have e : ((((t + 1).descFactorial (s + 1) : ℕ)) : ℚ) =
        ((((t + 1 - s : ℕ)))) * ((((t + 1).descFactorial s : ℕ)) : ℚ) := by
      exact_mod_cast congrArg Nat.cast hdf
    rw [e, hsub]
    ring
  · have hlt : t + 1 < s := Nat.lt_of_not_ge hle
    have hz1 : (t + 1).descFactorial s = 0 := Nat.descFactorial_of_lt hlt
    have hle2 : t + 1 < s + 1 := by omega
    have hz2 : (t + 1).descFactorial (s + 1) = 0 := Nat.descFactorial_of_lt hle2
    rw [hz1, hz2]
    simp

private lemma hA1B (m s : ℕ) :
    (∑ r ∈ Finset.range (m + 1 + 1),
        (-1 : ℚ) ^ r * ((((r + 1).factorial : ℕ)) : ℚ) *
          ((Nat.stirlingSecond (m + 1) r : ℕ) : ℚ) *
          ((((r + 1).descFactorial (s + 1) : ℕ)) : ℚ)) +
      (∑ t ∈ Finset.range (m + 1 + 1),
        (-1 : ℚ) ^ (t + 1) * ((((t + 1).factorial : ℕ)) : ℚ) *
          ((Nat.stirlingSecond (m + 1) t : ℕ) : ℚ) *
          ((((t + 1 + 1).descFactorial (s + 1) : ℕ)) : ℚ)) =
      -((s + 1 : ℕ) : ℚ) *
        (∑ t ∈ Finset.range (m + 1 + 1),
          (-1 : ℚ) ^ t * ((((t + 1).factorial : ℕ)) : ℚ) *
            ((Nat.stirlingSecond (m + 1) t : ℕ) : ℚ) *
            ((((t + 1).descFactorial s : ℕ)) : ℚ)) := by
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro r hr
  have hP := descFactorial_pascal_Q (r + 1) s
  have hsign : (-1 : ℚ) ^ (r + 1) = -(-1 : ℚ) ^ r := by
    rw [pow_succ]; ring
  rw [hsign]
  linear_combination -((-1 : ℚ) ^ r * ((((r + 1).factorial : ℕ)) : ℚ) *
    ((Nat.stirlingSecond (m + 1) r : ℕ) : ℚ)) * hP

private lemma hM (m s : ℕ) :
    (∑ t ∈ Finset.range (m + 1 + 1),
          (-1 : ℚ) ^ t * ((((t + 1).factorial : ℕ)) : ℚ) *
            ((Nat.stirlingSecond (m + 1) t : ℕ) : ℚ) *
            ((((t + 1).descFactorial s : ℕ)) : ℚ)) =
      Hsum (m + 1) (s + 1) + ((s : ℕ) : ℚ) * Hsum (m + 1) s := by
  unfold Hsum
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro r hr
  have hB := mul_descFactorial_eq r s
  have hf : ((((r + 1).factorial : ℕ)) : ℚ) =
      (((r + 1 : ℕ)) : ℚ) * ((((r).factorial : ℕ)) : ℚ) := by
    exact_mod_cast Nat.factorial_succ r
  rw [hf]
  linear_combination (-1 : ℚ) ^ r * ((Nat.stirlingSecond (m + 1) r : ℕ) : ℚ) *
    ((r.factorial : ℕ) : ℚ) * hB

private lemma hzS' (m : ℕ) : Nat.stirlingSecond (m + 1) (m + 1 + 1) = 0 :=
  Nat.stirlingSecond_eq_zero_of_lt (by omega)

private lemma hHrfl (m s : ℕ) : Hsum (m + 1) (s + 1) =
    (∑ r ∈ Finset.range (m + 1 + 1),
      (-1 : ℚ) ^ r * ((r.factorial : ℕ) : ℚ) *
        ((Nat.stirlingSecond (m + 1) r : ℕ) : ℚ) *
        ((((r + 1).descFactorial (s + 1) : ℕ)) : ℚ)) := by
  rfl

private lemma stirling_split_unif (m r : ℕ) :
    Nat.stirlingSecond (m + 1 + 1) r =
    r * Nat.stirlingSecond (m + 1) r + Nat.stirlingSecond (m + 1) (r - 1) := by
  cases r with
  | zero =>
    simp [Nat.stirlingSecond_succ_zero, Nat.stirlingSecond_succ_zero]
  | succ k =>
    simp only [Nat.add_sub_cancel]
    exact Nat.stirlingSecond_succ_succ (m + 1) k

private lemma Bshift (m s : ℕ) :
    (∑ r ∈ Finset.range (m + 1 + 1 + 1),
      (-1 : ℚ) ^ r * ((r.factorial : ℕ) : ℚ) * ((Nat.stirlingSecond (m + 1) (r - 1) : ℕ) : ℚ) *
        ((((r + 1).descFactorial (s + 1) : ℕ)) : ℚ)) =
    ∑ t ∈ Finset.range (m + 1 + 1),
      (-1 : ℚ) ^ (t + 1) * ((((t + 1).factorial : ℕ)) : ℚ) * ((Nat.stirlingSecond (m + 1) t : ℕ) : ℚ) *
        ((((t + 1 + 1).descFactorial (s + 1) : ℕ)) : ℚ) := by
  rw [Finset.sum_range_succ']
  have h0 : (-1 : ℚ) ^ 0 * ((Nat.factorial 0 : ℕ) : ℚ) * ((Nat.stirlingSecond (m + 1) (0 - 1) : ℕ) : ℚ) *
      ((((0 + 1).descFactorial (s + 1) : ℕ)) : ℚ) = 0 := by
    simp only [Nat.zero_sub]
    simp [Nat.stirlingSecond_succ_zero]
  rw [h0, add_zero]
  apply Finset.sum_congr rfl
  intro t ht
  simp only [Nat.add_sub_cancel]

private lemma hAfull (m s : ℕ) :
    (∑ r ∈ Finset.range (m + 1 + 1 + 1),
      (-1 : ℚ) ^ r * (((r : ℕ)) : ℚ) * ((r.factorial : ℕ) : ℚ) *
        ((Nat.stirlingSecond (m + 1) r : ℕ) : ℚ) *
        ((((r + 1).descFactorial (s + 1) : ℕ)) : ℚ)) =
    (∑ r ∈ Finset.range (m + 1 + 1 + 1),
      (-1 : ℚ) ^ r * ((((r + 1).factorial : ℕ)) : ℚ) *
        ((Nat.stirlingSecond (m + 1) r : ℕ) : ℚ) *
        ((((r + 1).descFactorial (s + 1) : ℕ)) : ℚ)) -
    (∑ r ∈ Finset.range (m + 1 + 1 + 1),
      (-1 : ℚ) ^ r * ((r.factorial : ℕ) : ℚ) *
        ((Nat.stirlingSecond (m + 1) r : ℕ) : ℚ) *
        ((((r + 1).descFactorial (s + 1) : ℕ)) : ℚ)) := by
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro r hr
  have hf : ((((r + 1).factorial : ℕ)) : ℚ) =
      (((r + 1 : ℕ)) : ℚ) * ((((r).factorial : ℕ)) : ℚ) := by
    exact_mod_cast Nat.factorial_succ r
  have hc : ((((r : ℕ))) : ℚ) = (((r + 1 : ℕ)) : ℚ) - 1 := by
    push_cast; ring
  rw [hf, hc]
  ring

private lemma hA1red (m s : ℕ) :
    (∑ r ∈ Finset.range (m + 1 + 1 + 1),
      (-1 : ℚ) ^ r * ((((r + 1).factorial : ℕ)) : ℚ) *
        ((Nat.stirlingSecond (m + 1) r : ℕ) : ℚ) *
        ((((r + 1).descFactorial (s + 1) : ℕ)) : ℚ)) =
    (∑ r ∈ Finset.range (m + 1 + 1),
      (-1 : ℚ) ^ r * ((((r + 1).factorial : ℕ)) : ℚ) *
        ((Nat.stirlingSecond (m + 1) r : ℕ) : ℚ) *
        ((((r + 1).descFactorial (s + 1) : ℕ)) : ℚ)) := by
  have htop : (-1 : ℚ) ^ (m + 1 + 1) * (((((m + 1 + 1) + 1).factorial : ℕ)) : ℚ) *
      ((Nat.stirlingSecond (m + 1) (m + 1 + 1) : ℕ) : ℚ) *
      ((((((m + 1 + 1) + 1)).descFactorial (s + 1) : ℕ)) : ℚ) = 0 := by
    rw [hzS' m]; simp
  have h := Finset.sum_range_succ (fun r =>
    (-1 : ℚ) ^ r * ((((r + 1).factorial : ℕ)) : ℚ) *
      ((Nat.stirlingSecond (m + 1) r : ℕ) : ℚ) *
      ((((r + 1).descFactorial (s + 1) : ℕ)) : ℚ)) (m + 1 + 1)
  rw [h, htop, add_zero]

private lemma hA2redExp (m s : ℕ) :
    (∑ r ∈ Finset.range (m + 1 + 1 + 1),
      (-1 : ℚ) ^ r * ((r.factorial : ℕ) : ℚ) *
        ((Nat.stirlingSecond (m + 1) r : ℕ) : ℚ) *
        ((((r + 1).descFactorial (s + 1) : ℕ)) : ℚ)) =
    (∑ r ∈ Finset.range (m + 1 + 1),
      (-1 : ℚ) ^ r * ((r.factorial : ℕ) : ℚ) *
        ((Nat.stirlingSecond (m + 1) r : ℕ) : ℚ) *
        ((((r + 1).descFactorial (s + 1) : ℕ)) : ℚ)) := by
  have htop : (-1 : ℚ) ^ (m + 1 + 1) * ((((m + 1 + 1).factorial : ℕ)) : ℚ) *
      ((Nat.stirlingSecond (m + 1) (m + 1 + 1) : ℕ) : ℚ) *
      (((((m + 1 + 1) + 1).descFactorial (s + 1) : ℕ)) : ℚ) = 0 := by
    rw [hzS' m]; simp
  have h := Finset.sum_range_succ (fun r =>
    (-1 : ℚ) ^ r * ((r.factorial : ℕ) : ℚ) *
      ((Nat.stirlingSecond (m + 1) r : ℕ) : ℚ) *
      ((((r + 1).descFactorial (s + 1) : ℕ)) : ℚ)) (m + 1 + 1)
  rw [h, htop, add_zero]

private lemma Hsum_succ_succ_aux (m s : ℕ) :
    Hsum (m + 1 + 1) (s + 1) =
    -((s + 2 : ℕ) : ℚ) * Hsum (m + 1) (s + 1) -
      ((s + 1 : ℕ) : ℚ) * (((s : ℕ)) : ℚ) * Hsum (m + 1) s := by
  have hAB : Hsum (m + 1 + 1) (s + 1) =
      (∑ r ∈ Finset.range (m + 1 + 1 + 1),
        (-1 : ℚ) ^ r * (((r : ℕ)) : ℚ) * ((r.factorial : ℕ) : ℚ) *
          ((Nat.stirlingSecond (m + 1) r : ℕ) : ℚ) *
          ((((r + 1).descFactorial (s + 1) : ℕ)) : ℚ)) +
      (∑ r ∈ Finset.range (m + 1 + 1 + 1),
        (-1 : ℚ) ^ r * ((r.factorial : ℕ) : ℚ) * ((Nat.stirlingSecond (m + 1) (r - 1) : ℕ) : ℚ) *
          ((((r + 1).descFactorial (s + 1) : ℕ)) : ℚ)) := by
    unfold Hsum
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro r hr
    have hS := stirling_split_unif m r
    have c : ((Nat.stirlingSecond (m + 1 + 1) r : ℕ) : ℚ) =
        (((r : ℕ)) : ℚ) * ((Nat.stirlingSecond (m + 1) r : ℕ) : ℚ) +
          ((Nat.stirlingSecond (m + 1) (r - 1) : ℕ) : ℚ) := by
      exact_mod_cast hS
    rw [c]
    ring
  rw [hAB, hAfull, hA1red, hA2redExp, ← hHrfl, Bshift, sub_add_eq_add_sub, hA1B, hM]
  push_cast
  ring
private lemma Hsum_one_zero : Hsum 1 0 = -Hsum 0 0 := by
  unfold Hsum
  simp [Finset.sum_range_succ, Nat.stirlingSecond_succ_zero, Nat.stirlingSecond_self]

private lemma Qshift_zero (m : ℕ) :
    (∑ k ∈ Finset.range (m + 1 + 1),
      (-1 : ℚ) ^ (k + 1) * (((k + 1).factorial : ℕ) : ℚ) *
        ((Nat.stirlingSecond (m + 1) k : ℕ) : ℚ)) =
    ∑ k ∈ Finset.range (m + 1),
      (-1 : ℚ) ^ k * (((k + 2).factorial : ℕ) : ℚ) *
        ((Nat.stirlingSecond (m + 1) (k + 1) : ℕ) : ℚ) := by
  rw [Finset.sum_range_succ']
  have h0 : (-1 : ℚ) ^ (0 + 1) * (((0 + 1).factorial : ℕ) : ℚ) *
      ((Nat.stirlingSecond (m + 1) 0 : ℕ) : ℚ) = 0 := by
    simp [Nat.stirlingSecond_succ_zero]
  rw [h0, add_zero]
  apply Finset.sum_congr rfl
  intro k hk
  have hpow : (-1 : ℚ) ^ (k + 1 + 1) = (-1 : ℚ) ^ k := by
    rw [show k + 1 + 1 = k + 2 from rfl]
    simp [pow_add]
  rw [hpow]

private lemma Hsum_succ_zero_aux (m : ℕ) : Hsum (m + 1 + 1) 0 = -Hsum (m + 1) 0 := by
  have hL : Hsum (m + 1 + 1) 0 =
      (∑ k ∈ Finset.range (m + 1 + 1),
        (-1 : ℚ) ^ (k + 1) * (((k + 1).factorial : ℕ) : ℚ) *
          ((((k + 1 : ℕ)) : ℚ) * ((Nat.stirlingSecond (m + 1) (k + 1) : ℕ) : ℚ))) +
      (∑ k ∈ Finset.range (m + 1 + 1),
        (-1 : ℚ) ^ (k + 1) * (((k + 1).factorial : ℕ) : ℚ) *
          ((Nat.stirlingSecond (m + 1) k : ℕ) : ℚ)) := by
    unfold Hsum
    simp only [Nat.descFactorial_zero, Nat.cast_one, mul_one]
    rw [Finset.sum_range_succ']
    have h0 : (-1 : ℚ) ^ 0 * ((Nat.factorial 0 : ℕ) : ℚ) *
        ((Nat.stirlingSecond (m + 1 + 1) 0 : ℕ) : ℚ) = 0 := by
      simp [Nat.stirlingSecond_succ_zero]
    rw [h0, add_zero]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    have hS := Nat.stirlingSecond_succ_succ (m + 1) k
    have c : ((Nat.stirlingSecond (m + 1 + 1) (k + 1) : ℕ) : ℚ) =
        (((k + 1 : ℕ)) : ℚ) * ((Nat.stirlingSecond (m + 1) (k + 1) : ℕ) : ℚ) +
          ((Nat.stirlingSecond (m + 1) k : ℕ) : ℚ) := by
      exact_mod_cast hS
    rw [c, mul_add]
  have hR : Hsum (m + 1) 0 =
      ∑ k ∈ Finset.range (m + 1),
        (-1 : ℚ) ^ (k + 1) * (((k + 1).factorial : ℕ) : ℚ) *
          ((Nat.stirlingSecond (m + 1) (k + 1) : ℕ) : ℚ) := by
    unfold Hsum
    simp only [Nat.descFactorial_zero, Nat.cast_one, mul_one]
    rw [Finset.sum_range_succ']
    have h0 : (-1 : ℚ) ^ 0 * ((Nat.factorial 0 : ℕ) : ℚ) *
        ((Nat.stirlingSecond (m + 1) 0 : ℕ) : ℚ) = 0 := by
      simp [Nat.stirlingSecond_succ_zero]
    rw [h0, add_zero]
  rw [hL, hR, Qshift_zero]
  have hPtop : (-1 : ℚ) ^ (m + 1 + 1) * ((((m + 1 + 1).factorial : ℕ)) : ℚ) *
      ((((m + 1 + 1 : ℕ)) : ℚ) * ((Nat.stirlingSecond (m + 1) (m + 1 + 1) : ℕ) : ℚ)) = 0 := by
    have hz : Nat.stirlingSecond (m + 1) (m + 1 + 1) = 0 :=
      Nat.stirlingSecond_eq_zero_of_lt (by omega)
    rw [hz]
    simp
  rw [Finset.sum_range_succ (fun k =>
    (-1 : ℚ) ^ (k + 1) * (((k + 1).factorial : ℕ) : ℚ) *
      ((((k + 1 : ℕ)) : ℚ) * ((Nat.stirlingSecond (m + 1) (k + 1) : ℕ) : ℚ)))]
  rw [hPtop, add_zero]
  rw [← Finset.sum_add_distrib, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  have hf : ((((k + 2).factorial : ℕ)) : ℚ) =
      (((k + 2 : ℕ)) : ℚ) * ((((k + 1).factorial : ℕ)) : ℚ) := by
    exact_mod_cast Nat.factorial_succ (k + 1)
  have hsign : (-1 : ℚ) ^ (k + 1) = -(-1 : ℚ) ^ k := by
    rw [pow_succ]
    ring
  rw [hf, hsign]
  push_cast
  ring

private lemma Hsum_succ_zero (n : ℕ) : Hsum (n + 1) 0 = -Hsum n 0 := by
  cases n with
  | zero => exact Hsum_one_zero
  | succ m => exact Hsum_succ_zero_aux m

private lemma Hsum_one_succ (s : ℕ) :
    Hsum 1 (s + 1) = -((s + 2 : ℕ) : ℚ) * Hsum 0 (s + 1) - ((s + 1 : ℕ) : ℚ) * ((s : ℕ) : ℚ) * Hsum 0 s := by
  unfold Hsum
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  simp only [Nat.stirlingSecond_succ_zero, Nat.cast_zero, zero_mul, mul_zero, add_zero,
    Nat.stirlingSecond_self, Nat.cast_one, mul_one]
  cases s with
  | zero =>
    have hA : (1 + 1 : ℕ).descFactorial (0 + 1) = 2 := by decide
    have hB : (0 + 1 : ℕ).descFactorial (0 + 1) = 1 := by decide
    have hC : (0 + 1 : ℕ).descFactorial 0 = 1 := by decide
    rw [hA, hB, hC]
    norm_num
  | succ k =>
    have e2 : (1 : ℕ).descFactorial (k + 1 + 1) = 0 := Nat.descFactorial_of_lt (by omega)
    rw [e2]
    simp only [Nat.cast_zero, mul_zero, add_zero]
    cases k with
    | zero =>
      have hA : (1 + 1 : ℕ).descFactorial (0 + 1 + 1) = 2 := by decide
      have hB : (0 + 1 : ℕ).descFactorial (0 + 1) = 1 := by decide
      rw [hA, hB]
      norm_num
    | succ j =>
      have f2 : (1 + 1 : ℕ).descFactorial (j + 1 + 1 + 1) = 0 :=
        Nat.descFactorial_of_lt (by omega)
      have f3 : (0 + 1 : ℕ).descFactorial (j + 1 + 1) = 0 :=
        Nat.descFactorial_of_lt (by omega)
      rw [f2, f3]
      simp

private noncomputable def Dsum (n s : ℕ) : ℚ :=
  ((s.factorial : ℕ) : ℚ) * (((s - 1).factorial : ℕ) : ℚ) * ((Nat.stirlingSecond (n + 1) s : ℕ) : ℚ) +
  (((s.factorial : ℕ)) : ℚ) ^ 2 * ((Nat.stirlingSecond (n + 1) (s + 1) : ℕ) : ℚ)

private lemma Dsum_zero (n : ℕ) : Dsum n 0 = 1 := by
  unfold Dsum
  simp only [Nat.zero_sub, Nat.factorial_zero, Nat.cast_one, one_mul,
    Nat.stirlingSecond_succ_zero, Nat.cast_zero, zero_add,
    Nat.stirlingSecond_one_right, Nat.cast_one, one_mul, one_pow, mul_one]

private lemma Dsum_succ (n s : ℕ) :
    Dsum (n + 1) (s + 1) =
    ((s + 2 : ℕ) : ℚ) * Dsum n (s + 1) + ((s + 1 : ℕ) : ℚ) * ((s : ℕ) : ℚ) * Dsum n s := by
  cases s with
  | zero =>
    rw [Dsum_zero]
    have hS := Nat.stirlingSecond_succ_succ (n + 1) 1
    norm_num at hS
    have h1 := Nat.stirlingSecond_one_right (n + 1)
    have h2 := Nat.stirlingSecond_one_right n
    unfold Dsum
    norm_num
    have c : ((Nat.stirlingSecond (n + 1 + 1) 2 : ℕ) : ℚ) =
        2 * ((Nat.stirlingSecond (n + 1) 2 : ℕ) : ℚ) + 1 := by
      have hS' : Nat.stirlingSecond (n + 1 + 1) 2 =
          2 * Nat.stirlingSecond (n + 1) 2 + Nat.stirlingSecond (n + 1) 1 := hS
      rw [hS']
      norm_num [h2]
    have e1 : ((Nat.stirlingSecond (n + 1 + 1) 1 : ℕ) : ℚ) = 1 := by exact_mod_cast h1
    have e2 : ((Nat.stirlingSecond (n + 1) 1 : ℕ) : ℚ) = 1 := by exact_mod_cast h2
    rw [e1, e2, c]
    ring
  | succ k =>
    have hS1 : Nat.stirlingSecond ((n + 1) + 1) (k + 1 + 1) =
        (k + 1 + 1) * Nat.stirlingSecond (n + 1) (k + 1 + 1) + Nat.stirlingSecond (n + 1) (k + 1) :=
      Nat.stirlingSecond_succ_succ (n + 1) (k + 1)
    have hS2 : Nat.stirlingSecond ((n + 1) + 1) ((k + 1 + 1) + 1) =
        ((k + 1 + 1) + 1) * Nat.stirlingSecond (n + 1) ((k + 1 + 1) + 1) +
        Nat.stirlingSecond (n + 1) (k + 1 + 1) :=
      Nat.stirlingSecond_succ_succ (n + 1) (k + 1 + 1)
    have c1 : ((Nat.stirlingSecond ((n + 1) + 1) (k + 1 + 1) : ℕ) : ℚ) =
        ((k + 1 + 1 : ℕ) : ℚ) * ((Nat.stirlingSecond (n + 1) (k + 1 + 1) : ℕ) : ℚ) +
        ((Nat.stirlingSecond (n + 1) (k + 1) : ℕ) : ℚ) := by
      exact_mod_cast hS1
    have c2 : ((Nat.stirlingSecond ((n + 1) + 1) ((k + 1 + 1) + 1) : ℕ) : ℚ) =
        ((((k + 1 + 1) + 1 : ℕ)) : ℚ) * ((Nat.stirlingSecond (n + 1) ((k + 1 + 1) + 1) : ℕ) : ℚ) +
        ((Nat.stirlingSecond (n + 1) (k + 1 + 1) : ℕ) : ℚ) := by
      exact_mod_cast hS2
    have hf1 : ((((k + 1 + 1).factorial : ℕ)) : ℚ) =
        (((k + 1 + 1 : ℕ)) : ℚ) * ((((k + 1).factorial : ℕ)) : ℚ) := by
      exact_mod_cast Nat.factorial_succ (k + 1)
    have hf2 : ((((k + 1).factorial : ℕ)) : ℚ) =
        (((k + 1 : ℕ)) : ℚ) * ((((k).factorial : ℕ)) : ℚ) := by
      exact_mod_cast Nat.factorial_succ k
    unfold Dsum
    simp only [Nat.add_sub_cancel]
    rw [c1, c2, hf1, hf2]
    push_cast
    ring

private lemma Hsum_succ_succ (n s : ℕ) :
    Hsum (n + 1) (s + 1) =
    -((s + 2 : ℕ) : ℚ) * Hsum n (s + 1) -
      ((s + 1 : ℕ) : ℚ) * (((s : ℕ)) : ℚ) * Hsum n s := by
  cases n with
  | zero => exact Hsum_one_succ s
  | succ m => exact Hsum_succ_succ_aux m s

private lemma Hbase (s : ℕ) : Hsum 0 s = Dsum 0 s := by
  unfold Hsum Dsum
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  simp only [Nat.stirlingSecond_zero, Nat.cast_one, one_mul, mul_one,
    Nat.factorial_zero, pow_zero]
  cases s with
  | zero =>
    simp [Nat.stirlingSecond_self, Nat.stirlingSecond_succ_zero]
  | succ k =>
    cases k with
    | zero =>
      have hz : Nat.stirlingSecond 1 2 = 0 :=
        Nat.stirlingSecond_eq_zero_of_lt (by omega)
      simp only [hz, Nat.cast_zero, mul_zero, add_zero]
      simp [Nat.stirlingSecond_self]
    | succ j =>
      have h1 : Nat.stirlingSecond 1 (j + 1 + 1) = 0 :=
        Nat.stirlingSecond_eq_zero_of_lt (by omega)
      have h2 : Nat.stirlingSecond 1 ((j + 1 + 1) + 1) = 0 :=
        Nat.stirlingSecond_eq_zero_of_lt (by omega)
      have h3 : (1 : ℕ).descFactorial (j + 1 + 1) = 0 :=
        Nat.descFactorial_of_lt (by omega)
      rw [h1, h2, h3]
      simp

private lemma keyCoeff : ∀ (n s : ℕ), Hsum n s = (-1 : ℚ) ^ n * Dsum n s := by
  intro n
  induction n with
  | zero =>
    intro s
    simp only [pow_zero, one_mul]
    exact Hbase s
  | succ n ih =>
    intro s
    cases s with
    | zero =>
      rw [Hsum_succ_zero, Dsum_zero, ih 0, Dsum_zero, pow_succ]
      ring
    | succ s =>
      rw [Hsum_succ_succ, Dsum_succ, ih (s + 1), ih s, pow_succ]
      push_cast
      ring

private noncomputable def Fsum (n k : ℕ) : ℚ :=
  (-1 : ℚ) ^ n * ∑ r ∈ Finset.range (n + 1),
    (-1 : ℚ) ^ r * (Nat.factorial r : ℚ) * (Nat.stirlingSecond n r : ℚ) *
      ((((r + 1) ^ k : ℕ)) : ℚ)

private noncomputable def Tsum (n k : ℕ) : ℚ :=
  ∑ s ∈ Finset.range (k + 1),
    ((Nat.stirlingSecond k s : ℕ) : ℚ) * Dsum n s

private lemma neg_one_pow_mul_self (n : ℕ) : (-1 : ℚ) ^ n * (-1 : ℚ) ^ n = 1 := by
  rcases Nat.even_or_odd n with h | h
  · rw [Even.neg_one_pow h]; norm_num
  · rw [Odd.neg_one_pow h]; norm_num

private lemma F_eq_T (n k : ℕ) : Fsum n k = Tsum n k := by
  have hexpand : ∀ r : ℕ, ((((r + 1) ^ k : ℕ)) : ℚ) =
      ∑ s ∈ Finset.range (k + 1),
        ((Nat.stirlingSecond k s : ℕ) : ℚ) * ((((r + 1).descFactorial s : ℕ)) : ℚ) := by
    intro r
    have h := Nat.pow_eq_sum_stirlingSecond_mul_descFactorial (r + 1) k
    have c : ((((r + 1) ^ k : ℕ)) : ℚ) =
        ((((∑ j ∈ Finset.range (k + 1),
          Nat.stirlingSecond k j * (r + 1).descFactorial j : ℕ))) : ℚ) := by
      exact_mod_cast congrArg Nat.cast h
    rw [c, Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro s hs
    simp [Nat.cast_mul]
  have hinner : ∀ s ∈ Finset.range (k + 1),
      (-1 : ℚ) ^ n *
        (∑ r ∈ Finset.range (n + 1),
          (-1 : ℚ) ^ r * (Nat.factorial r : ℚ) * (Nat.stirlingSecond n r : ℚ) *
            (((Nat.stirlingSecond k s : ℕ) : ℚ) * ((((r + 1).descFactorial s : ℕ)) : ℚ))) =
      ((Nat.stirlingSecond k s : ℕ) : ℚ) * Dsum n s := by
    intro s hs
    have hfac : (∑ r ∈ Finset.range (n + 1),
          (-1 : ℚ) ^ r * (Nat.factorial r : ℚ) * (Nat.stirlingSecond n r : ℚ) *
            (((Nat.stirlingSecond k s : ℕ) : ℚ) * ((((r + 1).descFactorial s : ℕ)) : ℚ))) =
        ((Nat.stirlingSecond k s : ℕ) : ℚ) * Hsum n s := by
      unfold Hsum
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r hr
      ring
    rw [hfac, keyCoeff n s]
    have h2 := neg_one_pow_mul_self n
    linear_combination ((Nat.stirlingSecond k s : ℕ) : ℚ) * Dsum n s * h2
  unfold Fsum Tsum
  simp only [hexpand]
  have step1 : (∑ r ∈ Finset.range (n + 1),
        (-1 : ℚ) ^ r * (Nat.factorial r : ℚ) * (Nat.stirlingSecond n r : ℚ) *
          (∑ s ∈ Finset.range (k + 1),
            ((Nat.stirlingSecond k s : ℕ) : ℚ) * ((((r + 1).descFactorial s : ℕ)) : ℚ))) =
      (∑ r ∈ Finset.range (n + 1), ∑ s ∈ Finset.range (k + 1),
        (-1 : ℚ) ^ r * (Nat.factorial r : ℚ) * (Nat.stirlingSecond n r : ℚ) *
          (((Nat.stirlingSecond k s : ℕ) : ℚ) * ((((r + 1).descFactorial s : ℕ)) : ℚ))) := by
    apply Finset.sum_congr rfl
    intro r hr
    exact Finset.mul_sum _ _ _
  rw [step1, Finset.sum_comm, Finset.mul_sum]
  exact Finset.sum_congr rfl hinner

private noncomputable def Gsum (n k : ℕ) : ℚ :=
  ∑ m ∈ Finset.range (k + 1),
    (((m.factorial : ℕ)) : ℚ) ^ 2 * ((Nat.stirlingSecond (n + 1) (m + 1) : ℕ) : ℚ) *
      ((Nat.stirlingSecond (k + 1) (m + 1) : ℕ) : ℚ)

private lemma Gshift (n k : ℕ) :
    (∑ m ∈ Finset.range (k + 1),
      (((m.factorial : ℕ)) : ℚ) ^ 2 * ((Nat.stirlingSecond (n + 1) (m + 1) : ℕ) : ℚ) *
        ((((m + 1 : ℕ))) : ℚ) * ((Nat.stirlingSecond k (m + 1) : ℕ) : ℚ)) =
    ∑ s ∈ Finset.range (k + 1),
      ((Nat.stirlingSecond k s : ℕ) : ℚ) * (((s : ℕ)) : ℚ) *
        ((((s - 1).factorial : ℕ)) : ℚ) ^ 2 * ((Nat.stirlingSecond (n + 1) s : ℕ) : ℚ) := by
  have hF0 : ((Nat.stirlingSecond k 0 : ℕ) : ℚ) * (((0 : ℕ)) : ℚ) *
      ((((0 - 1).factorial : ℕ)) : ℚ) ^ 2 * ((Nat.stirlingSecond (n + 1) 0 : ℕ) : ℚ) = 0 := by
    simp
  have hFtop : ((Nat.stirlingSecond k (k + 1) : ℕ) : ℚ) * ((((k + 1 : ℕ))) : ℚ) *
      ((((k + 1 - 1).factorial : ℕ)) : ℚ) ^ 2 * ((Nat.stirlingSecond (n + 1) (k + 1) : ℕ) : ℚ) = 0 := by
    have hz : Nat.stirlingSecond k (k + 1) = 0 :=
      Nat.stirlingSecond_eq_zero_of_lt (by omega)
    rw [hz]; simp
  have hbig : (∑ s ∈ Finset.range (k + 1 + 1),
        ((Nat.stirlingSecond k s : ℕ) : ℚ) * (((s : ℕ)) : ℚ) *
          ((((s - 1).factorial : ℕ)) : ℚ) ^ 2 * ((Nat.stirlingSecond (n + 1) s : ℕ) : ℚ)) =
      (∑ s ∈ Finset.range (k + 1),
        ((Nat.stirlingSecond k s : ℕ) : ℚ) * (((s : ℕ)) : ℚ) *
          ((((s - 1).factorial : ℕ)) : ℚ) ^ 2 * ((Nat.stirlingSecond (n + 1) s : ℕ) : ℚ)) := by
    rw [Finset.sum_range_succ, hFtop, add_zero]
  have hpeel : (∑ s ∈ Finset.range (k + 1 + 1),
        ((Nat.stirlingSecond k s : ℕ) : ℚ) * (((s : ℕ)) : ℚ) *
          ((((s - 1).factorial : ℕ)) : ℚ) ^ 2 * ((Nat.stirlingSecond (n + 1) s : ℕ) : ℚ)) =
      (∑ m ∈ Finset.range (k + 1),
        ((Nat.stirlingSecond k (m + 1) : ℕ) : ℚ) * ((((m + 1 : ℕ))) : ℚ) *
          ((((m + 1 - 1).factorial : ℕ)) : ℚ) ^ 2 * ((Nat.stirlingSecond (n + 1) (m + 1) : ℕ) : ℚ)) +
      (((Nat.stirlingSecond k 0 : ℕ) : ℚ) * (((0 : ℕ)) : ℚ) *
        ((((0 - 1).factorial : ℕ)) : ℚ) ^ 2 * ((Nat.stirlingSecond (n + 1) 0 : ℕ) : ℚ)) :=
    Finset.sum_range_succ' _ _
  rw [← hbig, hpeel, hF0, add_zero]
  apply Finset.sum_congr rfl
  intro m hm
  have hs : m + 1 - 1 = m := Nat.add_sub_cancel m 1
  rw [hs]
  ring

private lemma G_eq_T (n k : ℕ) : Gsum n k = Tsum n k := by
  unfold Gsum Tsum
  have hsplit : ∀ m ∈ Finset.range (k + 1),
      (((m.factorial : ℕ)) : ℚ) ^ 2 * ((Nat.stirlingSecond (n + 1) (m + 1) : ℕ) : ℚ) *
        ((Nat.stirlingSecond (k + 1) (m + 1) : ℕ) : ℚ) =
      ((((m.factorial : ℕ)) : ℚ) ^ 2 * ((Nat.stirlingSecond (n + 1) (m + 1) : ℕ) : ℚ) *
        ((((m + 1 : ℕ))) : ℚ) * ((Nat.stirlingSecond k (m + 1) : ℕ) : ℚ)) +
      ((((m.factorial : ℕ)) : ℚ) ^ 2 * ((Nat.stirlingSecond (n + 1) (m + 1) : ℕ) : ℚ) *
        ((Nat.stirlingSecond k m : ℕ) : ℚ)) := by
    intro m hm
    have hS := Nat.stirlingSecond_succ_succ k m
    have c : ((Nat.stirlingSecond (k + 1) (m + 1) : ℕ) : ℚ) =
        ((((m + 1 : ℕ))) : ℚ) * ((Nat.stirlingSecond k (m + 1) : ℕ) : ℚ) +
          ((Nat.stirlingSecond k m : ℕ) : ℚ) := by
      exact_mod_cast hS
    rw [c]
    ring
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib, Gshift]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro s hs
  unfold Dsum
  cases s with
  | zero =>
    simp only [Nat.zero_sub, Nat.factorial_zero, Nat.cast_one, one_mul, one_pow,
      Nat.stirlingSecond_succ_zero, Nat.cast_zero, zero_mul, mul_zero,
      Nat.zero_add, Nat.stirlingSecond_one_right]
    ring
  | succ s' =>
    have hsub : s' + 1 - 1 = s' := Nat.add_sub_cancel s' 1
    have hf : ((((s' + 1).factorial : ℕ)) : ℚ) =
        ((((s' + 1 : ℕ))) : ℚ) * ((((s').factorial : ℕ)) : ℚ) := by
      exact_mod_cast Nat.factorial_succ s'
    rw [hsub, hf]
    push_cast
    ring

private noncomputable def BigG (n k : ℕ) : ℚ :=
  ∑ m ∈ Finset.range (n + k + 1),
    (((m.factorial : ℕ)) : ℚ) ^ 2 * ((Nat.stirlingSecond (n + 1) (m + 1) : ℕ) : ℚ) *
      ((Nat.stirlingSecond (k + 1) (m + 1) : ℕ) : ℚ)

private lemma Gsum_eq_BigG (n k : ℕ) : Gsum n k = BigG n k := by
  unfold Gsum BigG
  apply Finset.sum_subset (Finset.range_mono (by omega : k + 1 ≤ n + k + 1))
  intro m hm hnm
  simp only [Finset.mem_range] at hm hnm
  have hle : k + 1 ≤ m := not_lt.mp hnm
  have hz : Nat.stirlingSecond (k + 1) (m + 1) = 0 :=
    Nat.stirlingSecond_eq_zero_of_lt (by omega)
  rw [hz]
  simp

private lemma BigG_symm (n k : ℕ) : BigG n k = BigG k n := by
  unfold BigG
  have hrange : n + k + 1 = k + n + 1 := by omega
  rw [hrange]
  apply Finset.sum_congr rfl
  intro m hm
  ring

private lemma Fsum_symm (n k : ℕ) : Fsum n k = Fsum k n := by
  rw [F_eq_T, ← G_eq_T, Gsum_eq_BigG, BigG_symm, ← Gsum_eq_BigG, G_eq_T, ← F_eq_T]

private lemma polyBernoulli_neg_rw (n k : ℕ) (P : ℕ → ℤ → ℚ)
    (hP : ∀ n k, P n k = (-1 : ℚ) ^ n * ∑ r ∈ Finset.range (n + 1),
      (-1 : ℚ) ^ r * (Nat.factorial r : ℚ) * (Nat.stirlingSecond n r : ℚ) /
        ((((r + 1 : ℕ) : ℚ)) ^ k)) :
    P n (-(k : ℤ)) = Fsum n k := by
  rw [hP]
  unfold Fsum
  apply congrArg
  apply Finset.sum_congr rfl
  intro r hr
  have h2 : ((((r + 1 : ℕ) : ℚ)) ^ (-(k : ℤ))) = ((((r + 1) ^ k : ℕ) : ℚ))⁻¹ := by
    rw [zpow_neg, zpow_natCast, Nat.cast_pow]
  rw [h2, div_eq_mul_inv, inv_inv]

namespace MetaMathlibExt

@[expose] public section

open scoped BigOperators

/-- **Poly-Bernoulli numbers.** Let $S(n, r)$ denote the Stirling numbers of the second kind. For
a natural number $n$ and an integer $k$, the poly-Bernoulli number $B_n^{(k)}$ is the rational
number given by Kaneko's explicit formula
$$B_n^{(k)} = (-1)^n \sum_{r=0}^{n} \frac{(-1)^r\, r!\, S(n, r)}{(r+1)^k}.$$

Introduced by M. Kaneko, "Poly-Bernoulli numbers," Journal de Théorie des
Nombres de Bordeaux 9 (1997), 221–228; see also T. Arakawa and M. Kaneko,
"On poly-Bernoulli numbers," Commentarii Mathematici Universitatis
Sancti Pauli 48 (1999), 159–167, as cited by the source.

Source: Y. Hamahata and H. Masubuchi, "Special Multi-Poly-Bernoulli Numbers,"
Journal of Integer Sequences 10 (2007), Article 07.4.1,
<https://cs.uwaterloo.ca/journals/JIS/VOL10/Hamahata/hamahata3.tex>.
The poly-Bernoulli generating-series definition and Kaneko's formula are
lines 106–152 of the official TeX. -/
def polyBernoulli (n : ℕ) (k : ℤ) : ℚ :=
  (-1 : ℚ) ^ n * ∑ r ∈ Finset.range (n + 1),
    (-1 : ℚ) ^ r * (Nat.factorial r : ℚ) * (Nat.stirlingSecond n r : ℚ) /
      (((r + 1 : ℕ) : ℚ) ^ k)

/-- **Arakawa–Kaneko duality for poly-Bernoulli numbers.** Let $S(n, r)$ denote the Stirling
numbers of the second kind. For a natural number $n$ and an integer $k$, let $B_n^{(k)}$ be the
poly-Bernoulli number given by Kaneko's explicit formula
$$B_n^{(k)} = (-1)^n \sum_{r=0}^{n} \frac{(-1)^r\, r!\, S(n, r)}{(r+1)^k}.$$
Then for all natural numbers $n$ and $k$,
$$B_n^{(-k)} = B_k^{(-n)}.$$

Source: Y. Hamahata and H. Masubuchi, "Special Multi-Poly-Bernoulli Numbers,"
Journal of Integer Sequences 10 (2007), Article 07.4.1,
<https://cs.uwaterloo.ca/journals/JIS/VOL10/Hamahata/hamahata3.tex>.
The symmetric closed formula and the duality are lines 156–174 of the
official TeX, attributed there to T. Arakawa and M. Kaneko,
"On poly-Bernoulli numbers," Commentarii Mathematici Universitatis
Sancti Pauli 48 (1999), 159–167.
Proves `Wanted` entry `arakawa_kaneko_duality`.
-/
theorem arakawa_kaneko_duality (n k : ℕ) :
    polyBernoulli n (-(k : ℤ)) = polyBernoulli k (-(n : ℤ)) := by
  have hP : ∀ a b, polyBernoulli a b = (-1 : ℚ) ^ a * ∑ r ∈ Finset.range (a + 1),
      (-1 : ℚ) ^ r * (Nat.factorial r : ℚ) * (Nat.stirlingSecond a r : ℚ) /
        ((((r + 1 : ℕ) : ℚ)) ^ b) := fun a b => rfl
  have e1 := polyBernoulli_neg_rw n k polyBernoulli hP
  have e2 := polyBernoulli_neg_rw k n polyBernoulli hP
  rw [e1, e2]
  exact Fsum_symm n k

end

end MetaMathlibExt
