/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Data.Int.Star
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import MathlibExt.Analysis.SpecialFunctions.JacobiTripleProduct

@[expose] public section

section
namespace MetaMathlibExt

/-! # Andrews form of Jacobi triple product
-/

private lemma ediv_two_mul_succ (k : ℕ) (M t : ℤ) (ht : M * (M + 1) = t + t) :
    (2 * (k : ℤ) + 1) * M * (M + 1) / 2 = (2 * (k : ℤ) + 1) * t := by
  have e : (2 * (k : ℤ) + 1) * M * (M + 1) = 2 * ((2 * (k : ℤ) + 1) * t) := by
    have e2 : (2 * (k : ℤ) + 1) * M * (M + 1)
        = (2 * (k : ℤ) + 1) * (M * (M + 1)) := by ring
    rw [e2, ht]; ring
  rw [e]; exact Int.mul_ediv_cancel_left _ two_ne_zero

private lemma int_exp_nonneg (k i : ℕ) (hi_le : i ≤ k) (n : ℤ) :
    0 ≤ (2 * (k : ℤ) + 1) * n * (n + 1) / 2 - (i : ℤ) * n := by
  have hIK : (i : ℤ) ≤ (k : ℤ) := by exact_mod_cast hi_le
  have h2E : (0 : ℤ) ≤ (2 * (k : ℤ) + 1) * n * (n + 1) - 2 * ((i : ℤ) * n) := by
    rcases lt_or_ge n 0 with hn | hn
    · have hm : (0 : ℤ) < -n := by omega
      have h1 : (0 : ℤ) ≤ n * (n + 1) := by
        have e : n * (n + 1) = (-n) * ((-n) - 1) := by ring
        rw [e]
        exact mul_nonneg (le_of_lt hm) (by omega)
      have h2 : (0 : ℤ) ≤ (2 * (k : ℤ) + 1) * (n * (n + 1)) :=
        mul_nonneg (by omega) h1
      have h3 : (0 : ℤ) ≤ -(2 * (i : ℤ) * n) := by
        have e : -(2 * (i : ℤ) * n) = 2 * (i : ℤ) * (-n) := by ring
        rw [e]
        exact mul_nonneg (mul_nonneg (by norm_num) (by positivity)) (le_of_lt hm)
      calc (0 : ℤ) ≤ (2 * (k : ℤ) + 1) * (n * (n + 1)) + (-(2 * (i : ℤ) * n)) :=
          add_nonneg h2 h3
        _ = (2 * (k : ℤ) + 1) * n * (n + 1) - 2 * ((i : ℤ) * n) := by ring
    · have h1 : (0 : ℤ) ≤ 2 * (k : ℤ) * n := mul_nonneg (by positivity) hn
      have e : (2 * (k : ℤ) + 1) * (n + 1) - 2 * (i : ℤ)
          = (2 * (k : ℤ) * n + (n + 1)) + 2 * ((k : ℤ) - (i : ℤ)) := by ring
      have h2 : (0 : ℤ) ≤ 2 * ((k : ℤ) - (i : ℤ)) := by omega
      have hinner : (0 : ℤ) ≤ (2 * (k : ℤ) + 1) * (n + 1) - 2 * (i : ℤ) := by omega
      calc (0 : ℤ) ≤ n * ((2 * (k : ℤ) + 1) * (n + 1) - 2 * (i : ℤ)) :=
          mul_nonneg hn hinner
        _ = (2 * (k : ℤ) + 1) * n * (n + 1) - 2 * ((i : ℤ) * n) := by ring
  obtain ⟨t, ht⟩ := Int.even_mul_succ_self n
  have hdiv : (2 * (k : ℤ) + 1) * n * (n + 1) / 2 = (2 * (k : ℤ) + 1) * t :=
    ediv_two_mul_succ k n t ht
  have hA : (2 * (k : ℤ) + 1) * n * (n + 1) = 2 * ((2 * (k : ℤ) + 1) * t) := by
    have e : (2 * (k : ℤ) + 1) * n * (n + 1)
        = (2 * (k : ℤ) + 1) * (n * (n + 1)) := by ring
    rw [e, ht]; ring
  rw [hdiv]
  rw [hA] at h2E
  omega

private lemma int_exp_lower (k i : ℕ) (hi_le : i ≤ k) (M : ℤ) (hM : 4 * (k : ℤ) + 4 ≤ M) :
    M ≤ (2 * (k : ℤ) + 1) * M * (M + 1) / 2 - (i : ℤ) * M := by
  have hIK : (i : ℤ) ≤ (k : ℤ) := by exact_mod_cast hi_le
  have hfac : (2 * (k : ℤ) + 1) * M * (M + 1) - (M + (i : ℤ) * M) * 2
      = M * ((2 * (k : ℤ) + 1) * (M + 1) - 2 * (i : ℤ) - 2) := by ring
  have h1 : (M + 1 : ℤ) ≤ (2 * (k : ℤ) + 1) * (M + 1) := by
    have h01 : (1 : ℤ) ≤ 2 * (k : ℤ) + 1 := by omega
    have h02 : (0 : ℤ) ≤ M + 1 := by omega
    calc (M + 1 : ℤ) = 1 * (M + 1) := (one_mul _).symm
      _ ≤ (2 * (k : ℤ) + 1) * (M + 1) := mul_le_mul_of_nonneg_right h01 h02
  have hV : (0 : ℤ) ≤ M * ((2 * (k : ℤ) + 1) * (M + 1) - 2 * (i : ℤ) - 2) :=
    mul_nonneg (by omega) (by omega)
  have hA : (M + (i : ℤ) * M) * 2 ≤ (2 * (k : ℤ) + 1) * M * (M + 1) := by omega
  obtain ⟨t, ht⟩ := Int.even_mul_succ_self M
  have hAeq : (2 * (k : ℤ) + 1) * M * (M + 1) = 2 * ((2 * (k : ℤ) + 1) * t) := by
    have e : (2 * (k : ℤ) + 1) * M * (M + 1)
        = (2 * (k : ℤ) + 1) * (M * (M + 1)) := by ring
    rw [e, ht]; ring
  have hdiv : (2 * (k : ℤ) + 1) * M * (M + 1) / 2 = (2 * (k : ℤ) + 1) * t := by
    rw [hAeq]; exact Int.mul_ediv_cancel_left _ two_ne_zero
  have hsle : M + (i : ℤ) * M ≤ (2 * (k : ℤ) + 1) * t := by omega
  rw [hdiv]
  omega

private lemma int_exp_neg_lower (k i : ℕ) (m : ℕ) :
    (m : ℤ) - 1 ≤ (2 * (k : ℤ) + 1) * (-(m : ℤ)) * ((-(m : ℤ)) + 1) / 2
      - (i : ℤ) * (-(m : ℤ)) := by
  obtain ⟨t, ht⟩ := Int.even_mul_succ_self (-(m : ℤ))
  have hring : (-(m : ℤ)) * ((-(m : ℤ)) + 1) = (m : ℤ) * ((m : ℤ) - 1) := by ring
  have ht' : (m : ℤ) * ((m : ℤ) - 1) = t + t := by rw [← hring]; exact ht
  have hdiv : (2 * (k : ℤ) + 1) * (-(m : ℤ)) * ((-(m : ℤ)) + 1) / 2
      = (2 * (k : ℤ) + 1) * t :=
    ediv_two_mul_succ k (-(m : ℤ)) t ht
  have ht0 : (0 : ℤ) ≤ t := by
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · push_cast at ht'
      omega
    · have h0 : (0 : ℤ) < (m : ℤ) := by exact_mod_cast hm
      have hprod : (0 : ℤ) ≤ (m : ℤ) * ((m : ℤ) - 1) :=
        mul_nonneg (by positivity) (by omega)
      omega
  have hmn : (0 : ℤ) ≤ ((m : ℤ) - 1) * ((m : ℤ) - 2) := by
    rcases lt_or_ge m 2 with h | h
    · interval_cases m <;> norm_num
    · have h2 : 2 ≤ m := h
      have h1 : (2 : ℤ) ≤ (m : ℤ) := by exact_mod_cast h2
      exact mul_nonneg (by omega) (by omega)
  have hlink : (m : ℤ) * ((m : ℤ) - 1) - (((m : ℤ) - 1) * ((m : ℤ) - 2))
      = 2 * ((m : ℤ) - 1) := by ring
  have htm1 : (m : ℤ) - 1 ≤ t := by omega
  have hKt : (t : ℤ) ≤ (2 * (k : ℤ) + 1) * t := by
    have e : (2 * (k : ℤ) + 1) * t - t = 2 * (k : ℤ) * t := by ring
    have hnn : (0 : ℤ) ≤ 2 * (k : ℤ) * t := mul_nonneg (by positivity) ht0
    omega
  have hIm : (0 : ℤ) ≤ (i : ℤ) * (m : ℤ) :=
    mul_nonneg (by positivity) (by positivity)
  have hY : (i : ℤ) * (-(m : ℤ)) = -((i : ℤ) * (m : ℤ)) := by ring
  rw [hdiv, hY]
  omega

private lemma norm_zpow_ge (q : ℂ) (hq : ‖q‖ < 1) (E : ℤ) (n : ℕ) (hE : 0 ≤ E)
    (hEn : n + 1 ≤ E.toNat) : ‖q ^ E‖ ≤ ‖q‖ * ‖q‖ ^ n := by
  have hnorm : ‖q ^ E‖ = ‖q‖ ^ E.toNat := by
    conv_lhs => rw [← Int.toNat_of_nonneg hE, zpow_natCast, norm_pow]
  rw [hnorm]
  calc ‖q‖ ^ E.toNat ≤ ‖q‖ ^ (n + 1) :=
        pow_le_pow_of_le_one (norm_nonneg _) hq.le hEn
    _ = ‖q‖ * ‖q‖ ^ n := by rw [pow_succ', mul_comm]

private lemma norm_series_term (q : ℂ) (s E : ℤ) (hE : 0 ≤ E) :
    ‖(-1 : ℂ) ^ s * q ^ E‖ = ‖q‖ ^ E.toNat := by
  conv_lhs => rw [norm_mul, norm_zpow, norm_neg, norm_one, one_zpow, one_mul,
    ← Int.toNat_of_nonneg hE, zpow_natCast, norm_pow]

private lemma toNat_ge_succ (E : ℤ) (n : ℕ) (h : ((n : ℤ) + 1) ≤ E) :
    n + 1 ≤ E.toNat := by
  have h2 := Int.toNat_le_toNat h
  have hc : ((((n : ℤ) + 1))).toNat = n + 1 := by
    have hc2 : ((n : ℤ) + 1) = ((((n + 1 : ℕ))) : ℤ) := by simp
    rw [hc2, Int.toNat_natCast]
  rwa [hc] at h2

private lemma summable_nonneg_side (q : ℂ) (k i : ℕ) (hi_le : i ≤ k) (hq : ‖q‖ < 1) :
    Summable (fun n : ℕ => (-1 : ℂ) ^ (n : ℤ) *
      q ^ ((2 * (k : ℤ) + 1) * (n : ℤ) * ((n : ℤ) + 1) / 2 - (i : ℤ) * (n : ℤ))) := by
  refine Summable.comp_nat_add (k := 4 * k + 4)
    (Summable.of_norm_bounded (g := fun n : ℕ => ‖q‖ ^ (4 * k + 4) * ‖q‖ ^ n) ?_ ?_)
  · exact (summable_geometric_of_lt_one (norm_nonneg _) hq).mul_left _
  · intro n
    have hM : 4 * (k : ℤ) + 4 ≤ ((((n + (4 * k + 4) : ℕ))) : ℤ) := by
      push_cast
      omega
    have hE := int_exp_lower k i hi_le _ hM
    have hEnn := int_exp_nonneg k i hi_le ((((n + (4 * k + 4) : ℕ))) : ℤ)
    rw [norm_series_term q _ _ hEnn]
    calc ‖q‖ ^ (((2 * (k : ℤ) + 1) * ((((n + (4 * k + 4) : ℕ))) : ℤ) *
        ((((((n + (4 * k + 4) : ℕ))) : ℤ)) + 1) / 2 -
        (i : ℤ) * ((((n + (4 * k + 4) : ℕ))) : ℤ))).toNat
        ≤ ‖q‖ ^ (n + (4 * k + 4)) := by
          apply pow_le_pow_of_le_one (norm_nonneg _) hq.le
          have h := Int.toNat_le_toNat hE
          rwa [Int.toNat_natCast] at h
      _ = ‖q‖ ^ (4 * k + 4) * ‖q‖ ^ n := by rw [add_comm n (4 * k + 4), pow_add]

private lemma summable_neg_side (q : ℂ) (k i : ℕ) (hi_le : i ≤ k) (hq : ‖q‖ < 1) :
    Summable (fun m : ℕ => (-1 : ℂ) ^ (-(m : ℤ)) *
      q ^ ((2 * (k : ℤ) + 1) * (-(m : ℤ)) * ((-(m : ℤ)) + 1) / 2 - (i : ℤ) * (-(m : ℤ)))) := by
  refine Summable.comp_nat_add (k := 1)
    (Summable.of_norm_bounded (g := fun m : ℕ => ‖q‖ ^ m) ?_ ?_)
  · exact summable_geometric_of_lt_one (norm_nonneg _) hq
  · intro m
    have hcast : ((((m + 1 : ℕ))) : ℤ) = (m : ℤ) + 1 := by
      rw [Nat.cast_add, Nat.cast_one]
    have hE0 := int_exp_neg_lower k i (m + 1)
    rw [hcast] at hE0 ⊢
    have h1 : (m : ℤ) + 1 - 1 = (m : ℤ) := by ring
    rw [h1] at hE0
    have hEnn := int_exp_nonneg k i hi_le (-((m : ℤ) + 1))
    rw [norm_series_term q _ _ hEnn]
    apply pow_le_pow_of_le_one (norm_nonneg _) hq.le
    have h := Int.toNat_le_toNat hE0
    rwa [Int.toNat_natCast] at h

private lemma multipliable_andrews (q : ℂ) (k i : ℕ) (hi_pos : 0 < i) (hi_le : i ≤ k)
    (hq : ‖q‖ < 1) :
    Multipliable (fun n : ℕ => (1 - q ^ ((2 * (k : ℤ) + 1) * ((n : ℤ) + 1))) *
      (1 - q ^ ((2 * (k : ℤ) + 1) * (n : ℤ) + (i : ℤ))) *
      (1 - q ^ ((2 * (k : ℤ) + 1) * ((n : ℤ) + 1) - (i : ℤ)))) := by
  have hIK : (i : ℤ) ≤ (k : ℤ) := by exact_mod_cast hi_le
  have hI1 : (1 : ℤ) ≤ (i : ℤ) := by exact_mod_cast hi_pos
  have e1 : ∀ n : ℕ, ((n : ℤ) + 1) ≤ (2 * (k : ℤ) + 1) * ((n : ℤ) + 1) := by
    intro n
    have h01 : (1 : ℤ) ≤ 2 * (k : ℤ) + 1 := by omega
    have h02 : (0 : ℤ) ≤ (n : ℤ) + 1 := by positivity
    calc ((n : ℤ) + 1) = 1 * ((n : ℤ) + 1) := (one_mul _).symm
      _ ≤ (2 * (k : ℤ) + 1) * ((n : ℤ) + 1) := mul_le_mul_of_nonneg_right h01 h02
  have e2 : ∀ n : ℕ, ((n : ℤ) + 1) ≤ (2 * (k : ℤ) + 1) * (n : ℤ) + (i : ℤ) := by
    intro n
    have h1 : (n : ℤ) ≤ (2 * (k : ℤ) + 1) * (n : ℤ) := by
      have e : (2 * (k : ℤ) + 1) * (n : ℤ) - (n : ℤ) = 2 * (k : ℤ) * (n : ℤ) := by ring
      have m : (0 : ℤ) ≤ 2 * (k : ℤ) * (n : ℤ) :=
        mul_nonneg (by positivity) (by positivity)
      omega
    omega
  have e3 : ∀ n : ℕ, ((n : ℤ) + 1) ≤ (2 * (k : ℤ) + 1) * ((n : ℤ) + 1) - (i : ℤ) := by
    intro n
    have e : (2 * (k : ℤ) + 1) * ((n : ℤ) + 1) - ((n : ℤ) + 1) - (i : ℤ)
        = (2 * (k : ℤ) * ((n : ℤ) + 1) - (k : ℤ)) + ((k : ℤ) - (i : ℤ)) := by ring
    have p1 : (0 : ℤ) ≤ 2 * (k : ℤ) * ((n : ℤ) + 1) - (k : ℤ) := by
      have e2 : 2 * (k : ℤ) * ((n : ℤ) + 1) - (k : ℤ)
          = (k : ℤ) * (2 * (n : ℤ) + 1) := by ring
      have m : (0 : ℤ) ≤ (k : ℤ) * (2 * (n : ℤ) + 1) :=
        mul_nonneg (by positivity) (by positivity)
      omega
    omega
  have s1 : Summable (fun n : ℕ => ‖q ^ ((2 * (k : ℤ) + 1) * ((n : ℤ) + 1))‖) := by
    refine Summable.of_nonneg_of_le
      (f := fun n : ℕ => ‖q‖ * ‖q‖ ^ n) (fun _ => norm_nonneg _) ?_ ?_
    · intro n
      have hE : (0 : ℤ) ≤ (2 * (k : ℤ) + 1) * ((n : ℤ) + 1) := by
        have h := e1 n
        have h02 : (0 : ℤ) ≤ (n : ℤ) + 1 := by positivity
        omega
      exact norm_zpow_ge q hq _ n hE (toNat_ge_succ _ n (e1 n))
    · exact (summable_geometric_of_lt_one (norm_nonneg _) hq).mul_left _
  have s2 : Summable (fun n : ℕ => ‖q ^ ((2 * (k : ℤ) + 1) * (n : ℤ) + (i : ℤ))‖) := by
    refine Summable.of_nonneg_of_le
      (f := fun n : ℕ => ‖q‖ * ‖q‖ ^ n) (fun _ => norm_nonneg _) ?_ ?_
    · intro n
      have hE : (0 : ℤ) ≤ (2 * (k : ℤ) + 1) * (n : ℤ) + (i : ℤ) := by
        have h := e2 n
        have h02 : (0 : ℤ) ≤ (n : ℤ) + 1 := by positivity
        omega
      exact norm_zpow_ge q hq _ n hE (toNat_ge_succ _ n (e2 n))
    · exact (summable_geometric_of_lt_one (norm_nonneg _) hq).mul_left _
  have s3 : Summable (fun n : ℕ => ‖q ^ ((2 * (k : ℤ) + 1) * ((n : ℤ) + 1) - (i : ℤ))‖) := by
    refine Summable.of_nonneg_of_le
      (f := fun n : ℕ => ‖q‖ * ‖q‖ ^ n) (fun _ => norm_nonneg _) ?_ ?_
    · intro n
      have hE : (0 : ℤ) ≤ (2 * (k : ℤ) + 1) * ((n : ℤ) + 1) - (i : ℤ) := by
        have h := e3 n
        have h02 : (0 : ℤ) ≤ (n : ℤ) + 1 := by positivity
        omega
      exact norm_zpow_ge q hq _ n hE (toNat_ge_succ _ n (e3 n))
    · exact (summable_geometric_of_lt_one (norm_nonneg _) hq).mul_left _
  have m1 : Multipliable (fun n : ℕ => 1 - q ^ ((2 * (k : ℤ) + 1) * ((n : ℤ) + 1))) :=
    multipliable_one_sub_of_summable s1
  have m2 : Multipliable (fun n : ℕ => 1 - q ^ ((2 * (k : ℤ) + 1) * (n : ℤ) + (i : ℤ))) :=
    multipliable_one_sub_of_summable s2
  have m3 : Multipliable (fun n : ℕ => 1 - q ^ ((2 * (k : ℤ) + 1) * ((n : ℤ) + 1) - (i : ℤ))) :=
    multipliable_one_sub_of_summable s3
  exact (m1.mul m2).mul m3

private lemma andrews_exp_pos (k i : ℕ) (hi_pos : 0 < i) (hi_le : i ≤ k)
    (n : ℤ) (hn : n ≠ 0) :
    0 < (2 * (k : ℤ) + 1) * n * (n + 1) / 2 - (i : ℤ) * n := by
  obtain ⟨t, ht⟩ := Int.even_mul_succ_self n
  have hdiv : (2 * (k : ℤ) + 1) * n * (n + 1) / 2 = (2 * (k : ℤ) + 1) * t :=
    ediv_two_mul_succ k n t ht
  rw [hdiv]
  have hI : (0 : ℤ) < (i : ℤ) := by exact_mod_cast hi_pos
  have hIK : (i : ℤ) ≤ (k : ℤ) := by exact_mod_cast hi_le
  have hk : (0 : ℤ) ≤ (k : ℤ) := by positivity
  have hNN : (0 : ℤ) ≤ n * (n + 1) := by
    rcases lt_or_ge n 0 with hneg | hpos
    · have h1 : n ≤ 0 := le_of_lt hneg
      have h2 : n + 1 ≤ 0 := by omega
      exact mul_nonneg_of_nonpos_of_nonpos h1 h2
    · have h2 : (0 : ℤ) ≤ n + 1 := by omega
      exact mul_nonneg hpos h2
  have ht0 : (0 : ℤ) ≤ t := by omega
  rcases ne_iff_lt_or_gt.mp hn with hneg | hpos
  · have hm : (0 : ℤ) < -n := by omega
    have hNt : (0 : ℤ) ≤ (2 * (k : ℤ) + 1) * t :=
      mul_nonneg (by omega) ht0
    have hIm : (0 : ℤ) < (i : ℤ) * (-n) :=
      mul_pos hI hm
    have heq : (2 * (k : ℤ) + 1) * t - (i : ℤ) * n =
        (2 * (k : ℤ) + 1) * t + (i : ℤ) * (-n) := by ring
    rw [heq]
    exact add_pos_of_nonneg_of_pos hNt hIm
  · have hkn : (0 : ℤ) ≤ (k : ℤ) * n := mul_nonneg hk (le_of_lt hpos)
    have hNp : (0 : ℤ) < (2 * (k : ℤ) + 1) * (n + 1) - 2 * (i : ℤ) := by
      have e : (2 * (k : ℤ) + 1) * (n + 1) - 2 * (i : ℤ) =
          2 * ((k : ℤ) * n) + 2 * ((k : ℤ) - (i : ℤ)) + (n + 1) := by ring
      rw [e]
      omega
    have hmul_pos : (0 : ℤ) < n * ((2 * (k : ℤ) + 1) * (n + 1) - 2 * (i : ℤ)) :=
      mul_pos hpos hNp
    have hEq : 2 * ((2 * (k : ℤ) + 1) * t - (i : ℤ) * n) =
        n * ((2 * (k : ℤ) + 1) * (n + 1) - 2 * (i : ℤ)) := by
      have ht2 : t + t = n * (n + 1) := ht.symm
      calc 2 * ((2 * (k : ℤ) + 1) * t - (i : ℤ) * n)
          = (2 * (k : ℤ) + 1) * (t + t) - 2 * ((i : ℤ) * n) := by ring
        _ = (2 * (k : ℤ) + 1) * (n * (n + 1)) - 2 * ((i : ℤ) * n) := by
            rw [ht2]
        _ = n * ((2 * (k : ℤ) + 1) * (n + 1) - 2 * (i : ℤ)) := by ring
    omega

private lemma andrews_zero_case (k i : ℕ) (hi_pos : 0 < i) (hi_le : i ≤ k) :
    ∑' n : ℤ, (-1 : ℂ) ^ n * (0 : ℂ) ^
        ((2 * (k : ℤ) + 1) * n * (n + 1) / 2 - (i : ℤ) * n) =
      ∏' n : ℕ, (1 - (0 : ℂ) ^ ((2 * (k : ℤ) + 1) * ((n : ℤ) + 1))) *
        (1 - (0 : ℂ) ^ ((2 * (k : ℤ) + 1) * (n : ℤ) + (i : ℤ))) *
        (1 - (0 : ℂ) ^ ((2 * (k : ℤ) + 1) * ((n : ℤ) + 1) - (i : ℤ))) := by
  have hExp0 : (2 * (k : ℤ) + 1) * (0 : ℤ) * ((0 : ℤ) + 1) / 2 - (i : ℤ) * (0 : ℤ)
      = 0 := by simp
  have hseries : (∑' n : ℤ, (-1 : ℂ) ^ n * (0 : ℂ) ^
        ((2 * (k : ℤ) + 1) * n * (n + 1) / 2 - (i : ℤ) * n)) = 1 := by
    have hsingle : ∀ n : ℤ, n ≠ 0 → (-1 : ℂ) ^ n * (0 : ℂ) ^
        ((2 * (k : ℤ) + 1) * n * (n + 1) / 2 - (i : ℤ) * n) = 0 := by
      intro n hn
      have hpos := andrews_exp_pos k i hi_pos hi_le n hn
      have hne : (2 * (k : ℤ) + 1) * n * (n + 1) / 2 - (i : ℤ) * n ≠ 0 :=
        ne_of_gt hpos
      rw [zero_zpow _ hne, mul_zero]
    have h0 : (-1 : ℂ) ^ (0 : ℤ) * (0 : ℂ) ^
        ((2 * (k : ℤ) + 1) * (0 : ℤ) * ((0 : ℤ) + 1) / 2 - (i : ℤ) * (0 : ℤ))
        = 1 := by
      rw [hExp0, zpow_zero, zpow_zero, one_mul]
    have hsum1 : (∑' n : ℤ, (-1 : ℂ) ^ n * (0 : ℂ) ^
          ((2 * (k : ℤ) + 1) * n * (n + 1) / 2 - (i : ℤ) * n)) =
        (-1 : ℂ) ^ (0 : ℤ) * (0 : ℂ) ^
          ((2 * (k : ℤ) + 1) * (0 : ℤ) * ((0 : ℤ) + 1) / 2 - (i : ℤ) * (0 : ℤ)) :=
      tsum_eq_single 0 hsingle
    rw [hsum1]
    exact h0
  have hprod : (∏' n : ℕ, (1 - (0 : ℂ) ^ ((2 * (k : ℤ) + 1) * ((n : ℤ) + 1))) *
        (1 - (0 : ℂ) ^ ((2 * (k : ℤ) + 1) * (n : ℤ) + (i : ℤ))) *
        (1 - (0 : ℂ) ^ ((2 * (k : ℤ) + 1) * ((n : ℤ) + 1) - (i : ℤ)))) = 1 := by
    have hone : ∀ m : ℕ, (1 - (0 : ℂ) ^ ((2 * (k : ℤ) + 1) * (((m : ℤ)) + 1))) *
          (1 - (0 : ℂ) ^ ((2 * (k : ℤ) + 1) * (m : ℤ) + (i : ℤ))) *
          (1 - (0 : ℂ) ^ ((2 * (k : ℤ) + 1) * (((m : ℤ)) + 1) - (i : ℤ))) = 1 := by
      intro m
      have hN : (0 : ℤ) < 2 * (k : ℤ) + 1 := by
        have hk : (0 : ℤ) ≤ (k : ℤ) := by positivity
        omega
      have hm0 : (0 : ℤ) ≤ (m : ℤ) := by positivity
      have hm1 : (0 : ℤ) < (m : ℤ) + 1 := by omega
      have hI : (0 : ℤ) < (i : ℤ) := by exact_mod_cast hi_pos
      have e1 : (0 : ℤ) < (2 * (k : ℤ) + 1) * ((m : ℤ) + 1) :=
        mul_pos hN hm1
      have e2 : (0 : ℤ) < (2 * (k : ℤ) + 1) * (m : ℤ) + (i : ℤ) := by
        have hNn : (0 : ℤ) ≤ (2 * (k : ℤ) + 1) * (m : ℤ) :=
          mul_nonneg (le_of_lt hN) hm0
        exact add_pos_of_nonneg_of_pos hNn hI
      have e3 : (0 : ℤ) < (2 * (k : ℤ) + 1) * ((m : ℤ) + 1) - (i : ℤ) := by
        have hle : ((m : ℤ) + 1) ≤
            (2 * (k : ℤ) + 1) * ((m : ℤ) + 1) - (i : ℤ) := by
          have e : (2 * (k : ℤ) + 1) * ((m : ℤ) + 1) - ((m : ℤ) + 1) - (i : ℤ) =
              (2 * (k : ℤ) * ((m : ℤ) + 1) - (k : ℤ)) + ((k : ℤ) - (i : ℤ)) := by
            ring
          have hIK : (i : ℤ) ≤ (k : ℤ) := by exact_mod_cast hi_le
          have p1 : (0 : ℤ) ≤ 2 * (k : ℤ) * ((m : ℤ) + 1) - (k : ℤ) := by
            have e2 : 2 * (k : ℤ) * ((m : ℤ) + 1) - (k : ℤ) =
                (k : ℤ) * (2 * (m : ℤ) + 1) := by ring
            have hk0 : (0 : ℤ) ≤ (k : ℤ) := by positivity
            have hm1' : (0 : ℤ) ≤ 2 * (m : ℤ) + 1 := by omega
            have mm : (0 : ℤ) ≤ (k : ℤ) * (2 * (m : ℤ) + 1) :=
              mul_nonneg hk0 hm1'
            omega
          omega
        omega
      have z1 : (0 : ℂ) ^ ((2 * (k : ℤ) + 1) * ((m : ℤ) + 1)) = 0 :=
        zero_zpow _ (ne_of_gt e1)
      have z2 : (0 : ℂ) ^ ((2 * (k : ℤ) + 1) * (m : ℤ) + (i : ℤ)) = 0 :=
        zero_zpow _ (ne_of_gt e2)
      have z3 : (0 : ℂ) ^ ((2 * (k : ℤ) + 1) * ((m : ℤ) + 1) - (i : ℤ)) = 0 :=
        zero_zpow _ (ne_of_gt e3)
      simp only [z1, z2, z3, sub_zero, mul_one]
    have hcongr : (∏' n : ℕ, (1 - (0 : ℂ) ^ ((2 * (k : ℤ) + 1) * ((n : ℤ) + 1))) *
          (1 - (0 : ℂ) ^ ((2 * (k : ℤ) + 1) * (n : ℤ) + (i : ℤ))) *
          (1 - (0 : ℂ) ^ ((2 * (k : ℤ) + 1) * ((n : ℤ) + 1) - (i : ℤ)))) =
        ∏' _ : ℕ, (1 : ℂ) :=
      tprod_congr hone
    rw [hcongr]
    exact tprod_one
  exact hseries.trans hprod.symm

private lemma andrews_sqrt (q : ℂ) (k : ℕ) (hq : ‖q‖ < 1) (hq0 : q ≠ 0) :
    ∃ r : ℂ, r ^ 2 = q ^ (2 * k + 1) ∧ ‖r‖ < 1 ∧ r ≠ 0 := by
  obtain ⟨r, hr⟩ := IsAlgClosed.exists_pow_nat_eq (q ^ (2 * k + 1)) (n := 2)
    zero_lt_two
  have hqN : q ^ (2 * k + 1) ≠ 0 := pow_ne_zero _ hq0
  have hr0 : r ≠ 0 := by
    intro hcon
    rw [hcon, zero_pow two_ne_zero] at hr
    exact hqN hr.symm
  have hnorm_eq : ‖r‖ ^ 2 = ‖q‖ ^ (2 * k + 1) := by
    have h := congrArg Norm.norm hr
    rwa [norm_pow, norm_pow] at h
  have hqpow : ‖q‖ ^ (2 * k + 1) < 1 :=
    pow_lt_one₀ (norm_nonneg _) hq (by omega)
  have hr2 : ‖r‖ ^ 2 < 1 := by
    rw [hnorm_eq]
    exact hqpow
  have hr1 : ‖r‖ < 1 :=
    (pow_lt_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp hr2
  exact ⟨r, hr, hr1, hr0⟩

private lemma andrews_series_term (q r : ℂ) (k i : ℕ) (hq0 : q ≠ 0) (hr0 : r ≠ 0)
    (hr2 : r ^ 2 = q ^ (2 * k + 1)) (n : ℤ) :
    (-r * (q ^ ((i : ℤ)))⁻¹) ^ n * r ^ (n * n).toNat =
      (-1 : ℂ) ^ n * q ^ ((2 * (k : ℤ) + 1) * n * (n + 1) / 2 - (i : ℤ) * n) := by
  obtain ⟨t, ht⟩ := Int.even_mul_succ_self n
  have hdiv : (2 * (k : ℤ) + 1) * n * (n + 1) / 2 = (2 * (k : ℤ) + 1) * t :=
    ediv_two_mul_succ k n t ht
  have hr2z : (r : ℂ) ^ ((2 : ℤ)) = q ^ ((2 * (k : ℤ) + 1)) := by
    have h1 : (r : ℂ) ^ ((((2 : ℕ)) : ℤ)) = q ^ ((((2 * k + 1 : ℕ)) : ℤ)) := by
      rw [zpow_natCast, zpow_natCast]
      exact hr2
    have h2 : ((((2 : ℕ)) : ℤ)) = (2 : ℤ) := by simp
    have h3 : ((((2 * k + 1 : ℕ)) : ℤ)) = 2 * (k : ℤ) + 1 := by
      push_cast
      ring
    rwa [h2, h3] at h1
  have hnn : (0 : ℤ) ≤ n * n := mul_self_nonneg n
  have hcast : ((((n * n).toNat : ℕ)) : ℤ) = n * n := Int.toNat_of_nonneg hnn
  have hr_nn : (r : ℂ) ^ (n * n).toNat = r ^ (n * n) := by
    rw [← zpow_natCast, hcast]
  have hz : (-r * (q ^ ((i : ℤ)))⁻¹) ^ n =
      (-1 : ℂ) ^ n * r ^ n * (((q ^ ((i : ℤ)))⁻¹) ^ n) := by
    have h1 : (-r * (q ^ ((i : ℤ)))⁻¹) = (-1) * r * ((q ^ ((i : ℤ)))⁻¹) := by
      ring
    rw [h1, mul_zpow, mul_zpow]
  have hqi : (((q ^ ((i : ℤ)))⁻¹) ^ n) = q ^ (-((i : ℤ) * n)) := by
    rw [inv_zpow, ← zpow_mul, zpow_neg]
  have hr_add : r ^ (n * n) * r ^ n = q ^ ((2 * (k : ℤ) + 1) * t) := by
    have h1 : r ^ (n * n) * r ^ n = r ^ (n * n + n) :=
      (zpow_add₀ hr0 _ _).symm
    have hexp : n * n + n = 2 * t := by
      have hnn1 : n * n + n = n * (n + 1) := by ring
      omega
    rw [h1, hexp, zpow_mul, hr2z, ← zpow_mul]
  have hq_add : q ^ ((2 * (k : ℤ) + 1) * t) * q ^ (-((i : ℤ) * n)) =
      q ^ ((2 * (k : ℤ) + 1) * n * (n + 1) / 2 - (i : ℤ) * n) := by
    have h1 : q ^ ((2 * (k : ℤ) + 1) * t) * q ^ (-((i : ℤ) * n)) =
        q ^ ((2 * (k : ℤ) + 1) * t + (-((i : ℤ) * n))) :=
      (zpow_add₀ hq0 _ _).symm
    rw [h1]
    congr 1
    omega
  calc (-r * (q ^ ((i : ℤ)))⁻¹) ^ n * r ^ (n * n).toNat
      = (-1 : ℂ) ^ n * r ^ n * (((q ^ ((i : ℤ)))⁻¹) ^ n) * r ^ (n * n) := by
        rw [hz, hr_nn]
    _ = (-1 : ℂ) ^ n * (r ^ (n * n) * r ^ n) * q ^ (-((i : ℤ) * n)) := by
        rw [hqi]
        ring
    _ = (-1 : ℂ) ^ n *
          (q ^ ((2 * (k : ℤ) + 1) * t) * q ^ (-((i : ℤ) * n))) := by
        rw [hr_add]
        ring
    _ = (-1 : ℂ) ^ n *
          q ^ ((2 * (k : ℤ) + 1) * n * (n + 1) / 2 - (i : ℤ) * n) := by
        rw [hq_add]

private lemma andrews_prod_factor (q r : ℂ) (k i : ℕ) (hq0 : q ≠ 0) (hr0 : r ≠ 0)
    (hr2 : r ^ 2 = q ^ (2 * k + 1)) (m : ℕ) :
    (1 - r ^ (2 * m + 2)) * (1 + (-r * (q ^ ((i : ℤ)))⁻¹) * r ^ (2 * m + 1)) *
      (1 + (-r * (q ^ ((i : ℤ)))⁻¹)⁻¹ * r ^ (2 * m + 1)) =
      (1 - q ^ ((2 * (k : ℤ) + 1) * ((m : ℤ) + 1))) *
        (1 - q ^ ((2 * (k : ℤ) + 1) * (m : ℤ) + (i : ℤ))) *
        (1 - q ^ ((2 * (k : ℤ) + 1) * ((m : ℤ) + 1) - (i : ℤ))) := by
  have e1 : r ^ (2 * m + 2) = q ^ ((2 * (k : ℤ) + 1) * ((m : ℤ) + 1)) := by
    have hpow : r ^ (2 * m + 2) = (r ^ 2) ^ (m + 1) := by
      have h : 2 * m + 2 = 2 * (m + 1) := by omega
      rw [h, pow_mul]
    rw [hpow, hr2, ← pow_mul]
    have hcast : ((((2 * k + 1) * (m + 1) : ℕ)) : ℤ) =
        (2 * (k : ℤ) + 1) * ((m : ℤ) + 1) := by
      push_cast
      ring
    rw [← zpow_natCast, hcast]
  have e0 : r ^ (2 * m) = q ^ ((2 * (k : ℤ) + 1) * (m : ℤ)) := by
    have hpow : r ^ (2 * m) = (r ^ 2) ^ m := by rw [pow_mul]
    rw [hpow, hr2, ← pow_mul]
    have hcast : ((((2 * k + 1) * m : ℕ)) : ℤ) =
        (2 * (k : ℤ) + 1) * (m : ℤ) := by
      push_cast
      ring
    rw [← zpow_natCast, hcast]
  have f1 : (1 - r ^ (2 * m + 2)) =
      (1 - q ^ ((2 * (k : ℤ) + 1) * ((m : ℤ) + 1))) := by
    rw [e1]
  have f3 : (1 + (-r * (q ^ ((i : ℤ)))⁻¹) * r ^ (2 * m + 1)) =
      (1 - q ^ ((2 * (k : ℤ) + 1) * ((m : ℤ) + 1) - (i : ℤ))) := by
    have hrr : r * r ^ (2 * m + 1) = r ^ (2 * m + 2) := by
      have h : r * r ^ (2 * m + 1) = r ^ 1 * r ^ (2 * m + 1) := by
        rw [pow_one]
      rw [h, ← pow_add]
      congr 1
      omega
    have hz_eq : (-r * (q ^ ((i : ℤ)))⁻¹) * r ^ (2 * m + 1) =
        -((r ^ (2 * m + 2)) * ((q ^ ((i : ℤ)))⁻¹)) := by ring
    have hmid : (-r * (q ^ ((i : ℤ)))⁻¹) * r ^ (2 * m + 1) =
        -(q ^ ((2 * (k : ℤ) + 1) * ((m : ℤ) + 1) - (i : ℤ))) := by
      rw [hz_eq, e1]
      have hq_inv : ((q ^ ((i : ℤ)))⁻¹) = q ^ (-((i : ℤ))) := by
        rw [zpow_neg]
      rw [hq_inv, ← zpow_add₀ hq0, ← sub_eq_add_neg]
    rw [hmid]
    exact (sub_eq_add_neg _ _).symm
  have f2 : (1 + (-r * (q ^ ((i : ℤ)))⁻¹)⁻¹ * r ^ (2 * m + 1)) =
      (1 - q ^ ((2 * (k : ℤ) + 1) * (m : ℤ) + (i : ℤ))) := by
    have hz_inv : (-r * (q ^ ((i : ℤ)))⁻¹)⁻¹ = (-r)⁻¹ * (q ^ ((i : ℤ))) := by
      rw [mul_inv_rev, inv_inv, mul_comm]
    have hneg_inv : (-r)⁻¹ = -(r⁻¹) := inv_neg
    have hr_inv_pow : r⁻¹ * r ^ (2 * m + 1) = r ^ (2 * m) := by
      have hpow : r ^ (2 * m + 1) = r ^ (2 * m) * r := pow_succ _ _
      calc r⁻¹ * r ^ (2 * m + 1)
          = r⁻¹ * (r ^ (2 * m) * r) := by rw [hpow]
        _ = r ^ (2 * m) * (r⁻¹ * r) := by ring
        _ = r ^ (2 * m) := by rw [inv_mul_cancel₀ hr0, mul_one]
    have hmid : (-r * (q ^ ((i : ℤ)))⁻¹)⁻¹ * r ^ (2 * m + 1) =
        -(q ^ ((2 * (k : ℤ) + 1) * (m : ℤ) + (i : ℤ))) := by
      rw [hz_inv, hneg_inv]
      have heq : (-(r⁻¹)) * (q ^ ((i : ℤ))) * r ^ (2 * m + 1) =
          -((r⁻¹ * r ^ (2 * m + 1)) * (q ^ ((i : ℤ)))) := by ring
      rw [heq, hr_inv_pow, e0, ← zpow_add₀ hq0]
    rw [hmid]
    exact (sub_eq_add_neg _ _).symm
  rw [f1, f3, f2, mul_right_comm]

/--
**Andrews' form of the Jacobi triple product identity.** Let $q$ be a complex number with
$|q| < 1$, and let $k$ and $i$ be natural numbers with $0 < i \le k$. Then
$$\sum_{n \in \mathbb{Z}} (-1)^n q^{(2k+1)n(n+1)/2 - in} =
\prod_{n=0}^{\infty} \left(1 - q^{(2k+1)(n+1)}\right) \left(1 - q^{(2k+1)n + i}\right)
\left(1 - q^{(2k+1)(n+1) - i}\right).$$

Proves `Wanted` entry `andrews_jacobi_triple_product`.

Source: Aritram Dhar, Avi Mukhopadhyay, and Rishabh Sarma, "Generalization of
the Extended Minimal Excludant of Andrews and Newman," Journal of Integer
Sequences 26 (2023), Article 23.3.7, Theorem (Andrews, An98 p. 22, label
JTP1), lines 459–462,
https://cs.uwaterloo.ca/journals/JIS/VOL26/Sarma/sarma5.tex
-/
theorem andrews_jacobi_triple_product
    (q : ℂ) (k i : ℕ) (hi_pos : 0 < i) (hi_le : i ≤ k) (hq : ‖q‖ < 1) :
    ∑' n : ℤ, (-1 : ℂ) ^ n * q ^ ((2 * (k : ℤ) + 1) * n * (n + 1) / 2 - (i : ℤ) * n) =
      ∏' n : ℕ, (1 - q ^ ((2 * (k : ℤ) + 1) * ((n : ℤ) + 1))) *
        (1 - q ^ ((2 * (k : ℤ) + 1) * (n : ℤ) + (i : ℤ))) *
        (1 - q ^ ((2 * (k : ℤ) + 1) * ((n : ℤ) + 1) - (i : ℤ))) := by
  by_cases hq0 : q = 0
  · subst hq0
    exact andrews_zero_case k i hi_pos hi_le
  · obtain ⟨r, hr2, hr1, hr0⟩ := andrews_sqrt q k hq hq0
    have hqI : q ^ ((i : ℤ)) ≠ 0 := zpow_ne_zero _ hq0
    have hz : (-r * (q ^ ((i : ℤ)))⁻¹) ≠ 0 :=
      mul_ne_zero (neg_ne_zero.mpr hr0) (inv_ne_zero hqI)
    obtain ⟨_, _, heq⟩ :=
      MetaMathlibExt.Analysis.SpecialFunctions.JacobiTripleProduct.jacobi_triple_product
        (-r * (q ^ ((i : ℤ)))⁻¹) r hz hr1
    have hseries : (∑' n : ℤ, (-r * (q ^ ((i : ℤ)))⁻¹) ^ n * r ^ (n * n).toNat) =
        (∑' n : ℤ, (-1 : ℂ) ^ n *
          q ^ ((2 * (k : ℤ) + 1) * n * (n + 1) / 2 - (i : ℤ) * n)) :=
      tsum_congr (fun n => andrews_series_term q r k i hq0 hr0 hr2 n)
    have hprod : (∏' n : ℕ, (1 - r ^ (2 * n + 2)) *
          (1 + (-r * (q ^ ((i : ℤ)))⁻¹) * r ^ (2 * n + 1)) *
          (1 + (-r * (q ^ ((i : ℤ)))⁻¹)⁻¹ * r ^ (2 * n + 1))) =
        (∏' n : ℕ, (1 - q ^ ((2 * (k : ℤ) + 1) * ((n : ℤ) + 1))) *
          (1 - q ^ ((2 * (k : ℤ) + 1) * (n : ℤ) + (i : ℤ))) *
          (1 - q ^ ((2 * (k : ℤ) + 1) * ((n : ℤ) + 1) - (i : ℤ)))) :=
      tprod_congr (fun m => andrews_prod_factor q r k i hq0 hr0 hr2 m)
    calc (∑' n : ℤ, (-1 : ℂ) ^ n *
            q ^ ((2 * (k : ℤ) + 1) * n * (n + 1) / 2 - (i : ℤ) * n))
        = (∑' n : ℤ, (-r * (q ^ ((i : ℤ)))⁻¹) ^ n * r ^ (n * n).toNat) :=
          hseries.symm
      _ = (∏' n : ℕ, (1 - r ^ (2 * n + 2)) *
            (1 + (-r * (q ^ ((i : ℤ)))⁻¹) * r ^ (2 * n + 1)) *
            (1 + (-r * (q ^ ((i : ℤ)))⁻¹)⁻¹ * r ^ (2 * n + 1))) := heq
      _ = (∏' n : ℕ, (1 - q ^ ((2 * (k : ℤ) + 1) * ((n : ℤ) + 1))) *
            (1 - q ^ ((2 * (k : ℤ) + 1) * (n : ℤ) + (i : ℤ))) *
            (1 - q ^ ((2 * (k : ℤ) + 1) * ((n : ℤ) + 1) - (i : ℤ)))) := hprod

/-- **Convergence of the series in Andrews' triple product identity.** Let $q$ be a complex
number with $|q| < 1$, and let $k$ and $i$ be natural numbers with $i \le k$. Then the bilateral
series
$$\sum_{n \in \mathbb{Z}} (-1)^n q^{(2k+1)n(n+1)/2 - in}$$
is summable over $\mathbb{Z}$. -/
theorem andrews_jacobi_triple_product_summable
    (q : ℂ) (k i : ℕ) (hi_le : i ≤ k) (hq : ‖q‖ < 1) :
    Summable (fun n : ℤ => (-1 : ℂ) ^ n *
      q ^ ((2 * (k : ℤ) + 1) * n * (n + 1) / 2 - (i : ℤ) * n)) := by
  have h1 : Summable (fun n : ℕ => (fun m : ℤ => (-1 : ℂ) ^ m *
      q ^ ((2 * (k : ℤ) + 1) * m * (m + 1) / 2 - (i : ℤ) * m)) (n : ℤ)) :=
    summable_nonneg_side q k i hi_le hq
  have h2 : Summable (fun n : ℕ => (fun m : ℤ => (-1 : ℂ) ^ m *
      q ^ ((2 * (k : ℤ) + 1) * m * (m + 1) / 2 - (i : ℤ) * m)) (-(n : ℤ))) :=
    summable_neg_side q k i hi_le hq
  exact Summable.of_nat_of_neg h1 h2

/-- **Convergence of the product in Andrews' triple product identity.** Let $q$ be a complex
number with $|q| < 1$, and let $k$ and $i$ be natural numbers with $0 < i \le k$. Then the infinite
product
$$\prod_{n=0}^{\infty} \left(1 - q^{(2k+1)(n+1)}\right) \left(1 - q^{(2k+1)n + i}\right)
\left(1 - q^{(2k+1)(n+1) - i}\right)$$
is multipliable: its products over finite sets of indices converge in $\mathbb{C}$
(unconditional convergence, where the limit is not required to be nonzero). -/
theorem andrews_jacobi_triple_product_multipliable
    (q : ℂ) (k i : ℕ) (hi_pos : 0 < i) (hi_le : i ≤ k) (hq : ‖q‖ < 1) :
    Multipliable (fun n : ℕ => (1 - q ^ ((2 * (k : ℤ) + 1) * ((n : ℤ) + 1))) *
      (1 - q ^ ((2 * (k : ℤ) + 1) * (n : ℤ) + (i : ℤ))) *
      (1 - q ^ ((2 * (k : ℤ) + 1) * ((n : ℤ) + 1) - (i : ℤ)))) :=
  multipliable_andrews q k i hi_pos hi_le hq

end MetaMathlibExt
end
