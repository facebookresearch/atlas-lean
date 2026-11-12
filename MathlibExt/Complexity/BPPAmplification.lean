/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Probability.ProbabilityMassFunction.Basic

@[expose] public section

/-! # BPP error amplification

Majority voting over `n` independent repetitions, each correct
with probability at least `2/3`, fails with probability at most
`exp (-n/18)`. This is roadmap package MOD-46 of the Atlas TCS
canon roadmap.

Source: Arora and Barak, Computational Complexity (2009),
Section 7.1.
-/

open Finset

/-- Majority vote of a tuple of Boolean votes. -/
def majority {n : ℕ} (v : Fin n → Bool) : Bool :=
  decide (n / 2 < (Finset.univ.filter (fun i => v i = true)).card)

private theorem sum_pi_mul : ∀ (n : ℕ) (g : Fin n → Bool → ℝ),
    (∑ v : Fin n → Bool, ∏ i, g i (v i)) = ∏ i, ∑ b, g i b
  | 0, _ => by simp
  | n + 1, g => by
    have hsum : (∑ v : Fin (n + 1) → Bool, ∏ i, g i (v i))
        = ∑ x : Bool × (Fin n → Bool), ∏ i, g i ((Fin.consEquiv (fun _ => Bool)) x i) :=
      (Equiv.sum_comp (Fin.consEquiv (fun _ => Bool)) _).symm
    rw [hsum]
    simp_rw [Fin.consEquiv_apply]
    simp_rw [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
    rw [Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum]
    rw [← Finset.sum_mul]
    have ih' : (∑ v : Fin n → Bool, ∏ (i : Fin n), g (i.succ) (v i))
        = ∏ (i : Fin n), ∑ b, g (i.succ) b :=
      sum_pi_mul n (fun i b => g (i.succ) b)
    rw [ih']

private theorem pmf_sum_bool (p : PMF Bool) : (p true).toReal + (p false).toReal = 1 := by
  have h1 : (∑' b : Bool, p b) = 1 := PMF.tsum_coe p
  rw [tsum_fintype] at h1
  have h2 : ((∑ b : Bool, p b).toReal) = (1 : ENNReal).toReal := by rw [h1]
  rw [ENNReal.toReal_sum (fun b _ => p.apply_ne_top b)] at h2
  rw [ENNReal.toReal_one] at h2
  rw [Fintype.sum_bool] at h2
  exact h2

private theorem card_true_eq (n : ℕ) (v : Fin n → Bool) :
    ((Finset.univ.filter (fun i => v i = true)).card : ℝ)
      = ∑ i : Fin n, (if v i = true then (1 : ℝ) else 0) := by
  have h : (Finset.univ.filter (fun i => v i = true)).card
      = ∑ i ∈ (Finset.univ : Finset (Fin n)), (if v i = true then 1 else 0) := by
    rw [Finset.card_filter]
  calc ((Finset.univ.filter (fun i => v i = true)).card : ℝ)
      = ((∑ i ∈ (Finset.univ : Finset (Fin n)), (if v i = true then 1 else 0)) : ℕ) := by rw [h]
    _ = ∑ i ∈ (Finset.univ : Finset (Fin n)), (if v i = true then (1 : ℝ) else 0) := by
        rw [Nat.cast_sum]
        apply Finset.sum_congr rfl
        intro i _
        split_ifs <;> simp
    _ = ∑ i : Fin n, (if v i = true then (1 : ℝ) else 0) := by rfl

private theorem bad_card_le (n : ℕ) (v : Fin n → Bool) (h : majority v = false) :
    ((Finset.univ.filter (fun i => v i = true)).card : ℝ) ≤ (n : ℝ) / 2 := by
  unfold majority at h
  have hneg : ¬ (n / 2 < (Finset.univ.filter (fun i => v i = true)).card) :=
    of_decide_eq_false h
  have h1 : (Finset.univ.filter (fun i => v i = true)).card ≤ n / 2 :=
    Nat.le_of_not_gt hneg
  have h2 : (n / 2 * 2) ≤ n := Nat.div_mul_le_self n 2
  have h3 : (((Finset.univ.filter (fun i => v i = true)).card : ℕ) : ℝ) ≤ ((n / 2 : ℕ) : ℝ) :=
    Nat.cast_le.mpr h1
  have h4 : ((n / 2 : ℕ) : ℝ) ≤ (n : ℝ) / 2 := by
    have h2r : ((n / 2 * 2 : ℕ) : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr h2
    push_cast at h2r
    linarith
  linarith

private theorem exp_split (n : ℕ) (v : Fin n → Bool) (s : ℝ) :
    s * ((n : ℝ) / 2 - ∑ i : Fin n, (if v i = true then (1 : ℝ) else 0))
      = ∑ i : Fin n, s * (1 / 2 - (if v i = true then (1 : ℝ) else 0)) := by
  have hn : (n : ℝ) = ∑ _i : Fin n, (1 : ℝ) := by simp
  have h2 : (∑ _i : Fin n, (1 : ℝ)) / 2 = ∑ _i : Fin n, ((1 : ℝ) / 2) := by
    rw [Finset.sum_div]
  calc s * ((n : ℝ) / 2 - ∑ i : Fin n, (if v i = true then (1 : ℝ) else 0))
      = s * ((∑ _i : Fin n, ((1 : ℝ) / 2)) - ∑ i : Fin n, (if v i = true then (1 : ℝ) else 0)) := by
        rw [hn, h2]
    _ = s * (∑ i : Fin n, ((1 : ℝ) / 2 - (if v i = true then (1 : ℝ) else 0))) := by
        rw [← Finset.sum_sub_distrib]
    _ = ∑ i : Fin n, s * (1 / 2 - (if v i = true then (1 : ℝ) else 0)) := by
        rw [Finset.mul_sum]

private theorem exp_half_log2 : Real.exp (Real.log 2 / 2) = Real.sqrt 2 := by
  have hs : Real.exp (Real.log 2) = 2 := Real.exp_log (by norm_num)
  have hpos : 0 < Real.exp (Real.log 2 / 2) := Real.exp_pos _
  have hsq : Real.exp (Real.log 2 / 2) * Real.exp (Real.log 2 / 2) = 2 := by
    have h : Real.exp (Real.log 2 / 2) * Real.exp (Real.log 2 / 2)
        = Real.exp (Real.log 2 / 2 + Real.log 2 / 2) := by
      rw [← Real.exp_add]
    rw [h]
    have hadd : Real.log 2 / 2 + Real.log 2 / 2 = Real.log 2 := by ring
    rw [hadd, hs]
  have hsqrt : Real.sqrt 2 = Real.exp (Real.log 2 / 2) := by
    rw [Real.sqrt_eq_iff_mul_self_eq_of_pos hpos]
    exact hsq
  exact hsqrt.symm

private theorem inv_sqrt2 : (Real.sqrt 2)⁻¹ = Real.sqrt 2 / 2 := by
  have h : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hne : Real.sqrt 2 ≠ 0 := by
    have hpos : (0:ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    exact ne_of_gt hpos
  have h2 : (Real.sqrt 2)⁻¹ * 2 = Real.sqrt 2 := by
    calc (Real.sqrt 2)⁻¹ * 2
        = (Real.sqrt 2)⁻¹ * (Real.sqrt 2 * Real.sqrt 2) := by rw [h]
      _ = ((Real.sqrt 2)⁻¹ * Real.sqrt 2) * Real.sqrt 2 := by ring
      _ = 1 * Real.sqrt 2 := by rw [inv_mul_cancel₀ hne]
      _ = Real.sqrt 2 := by ring
  have h3 : (Real.sqrt 2)⁻¹ = Real.sqrt 2 / 2 := by
    rw [eq_div_iff (by norm_num)]
    exact h2
  exact h3

private theorem pervote_bound (p : PMF Bool) (hp : (2/3 : ℝ) ≤ (p true).toReal) :
    ∑ b : Bool, (p b).toReal * Real.exp (Real.log 2 * (1/2 - (if b = true then (1:ℝ) else 0)))
      ≤ 2 * Real.sqrt 2 / 3 := by
  have hsum : ∑ b : Bool, (p b).toReal * Real.exp (Real.log 2 * (1/2 - (if b = true then (1:ℝ) else 0)))
      = (p true).toReal * Real.exp (Real.log 2 * (1/2 - 1))
        + (p false).toReal * Real.exp (Real.log 2 * (1/2 - 0)) := by
    rw [Fintype.sum_bool]
    simp
  rw [hsum]
  have e1 : Real.log 2 * (1/2 - (1:ℝ)) = -(Real.log 2 / 2) := by ring
  have e2 : Real.log 2 * (1/2 - (0:ℝ)) = Real.log 2 / 2 := by ring
  rw [e1, e2]
  rw [exp_half_log2]
  have hexp_neg : Real.exp (-(Real.log 2 / 2)) = (Real.sqrt 2)⁻¹ := by
    rw [Real.exp_neg, exp_half_log2]
  rw [hexp_neg, inv_sqrt2]
  have hpmf := pmf_sum_bool p
  have hq_le : (p true).toReal ≤ 1 := by
    have hqf_nn : 0 ≤ (p false).toReal := ENNReal.toReal_nonneg
    linarith [hpmf]
  have hfalse_eq : (p false).toReal = 1 - (p true).toReal := by linarith [hpmf]
  rw [hfalse_eq]
  have hpos : (0:ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hBA : Real.sqrt 2 / 2 - Real.sqrt 2 ≤ 0 := by
    have : (0:ℝ) ≤ Real.sqrt 2 := le_of_lt hpos
    linarith
  have hmono : (p true).toReal * (Real.sqrt 2 / 2 - Real.sqrt 2)
      ≤ (2/3) * (Real.sqrt 2 / 2 - Real.sqrt 2) :=
    mul_le_mul_of_nonpos_right hp hBA
  have hlhs : (p true).toReal * (Real.sqrt 2 / 2) + (1 - (p true).toReal) * Real.sqrt 2
      = Real.sqrt 2 + (p true).toReal * (Real.sqrt 2 / 2 - Real.sqrt 2) := by ring
  have hrhs : (2:ℝ) * Real.sqrt 2 / 3 = Real.sqrt 2 + (2/3) * (Real.sqrt 2 / 2 - Real.sqrt 2) := by ring
  rw [hlhs, hrhs]
  linarith [hmono]

private theorem exp_one18_le : Real.exp ((1 : ℝ) / 18) ≤ 18 / 17 := by
  have h1 : ((17 : ℝ) / 18) ≤ Real.exp (-((1 : ℝ) / 18)) := by
    have h := Real.add_one_le_exp (-((1 : ℝ) / 18))
    have heq : (-((1 : ℝ) / 18)) + 1 = 17 / 18 := by ring
    rw [heq] at h
    exact h
  have hpos1 : (0 : ℝ) < 17 / 18 := by norm_num
  have hpos2 : (0 : ℝ) < Real.exp (-((1 : ℝ) / 18)) := Real.exp_pos _
  have hexp : Real.exp ((1 : ℝ) / 18) = (Real.exp (-((1 : ℝ) / 18)))⁻¹ := by
    have h := Real.exp_neg (-((1 : ℝ) / 18))
    have heq : -(-((1 : ℝ) / 18)) = (1 : ℝ) / 18 := by ring
    rw [heq] at h
    exact h
  rw [hexp]
  have hinv : ((17 : ℝ) / 18)⁻¹ = 18 / 17 := by norm_num
  rw [← hinv]
  rw [inv_le_inv₀ hpos2 hpos1]
  exact h1

private theorem sqrt2_bound : 12 * Real.sqrt 2 ≤ 17 := by
  have hsq : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hnn : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  nlinarith [hsq, hnn, sq_nonneg (12 * Real.sqrt 2 - 17)]

private theorem key_numeric : (2 : ℝ) * Real.sqrt 2 / 3 ≤ Real.exp (-((1 : ℝ) / 18)) := by
  have h1 : Real.exp ((1 : ℝ) / 18) ≤ 18 / 17 := exp_one18_le
  have h2 : (18 : ℝ) / 17 ≤ 3 / (2 * Real.sqrt 2) := by
    have hpos : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    have hsqrt_bound : 12 * Real.sqrt 2 ≤ 17 := sqrt2_bound
    rw [div_le_div_iff₀ (by norm_num) (by positivity)]
    nlinarith [hsqrt_bound]
  have hpos1 : (0 : ℝ) < Real.exp ((1 : ℝ) / 18) := Real.exp_pos _
  have hexp : Real.exp (-((1 : ℝ) / 18)) = (Real.exp ((1 : ℝ) / 18))⁻¹ := by
    rw [Real.exp_neg]
  rw [hexp]
  have h3 : (3 : ℝ) / (2 * Real.sqrt 2) = ((2 * Real.sqrt 2 / 3))⁻¹ := by
    field_simp
  have h4 : Real.exp ((1 : ℝ) / 18) ≤ ((2 * Real.sqrt 2 / 3))⁻¹ := by
    rw [← h3]
    calc Real.exp ((1 : ℝ) / 18) ≤ 18 / 17 := h1
      _ ≤ 3 / (2 * Real.sqrt 2) := h2
  have hpos3 : (0 : ℝ) < 2 * Real.sqrt 2 / 3 := by
    have hpos : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    positivity
  have hbinv_pos : (0 : ℝ) < ((2 * Real.sqrt 2 / 3))⁻¹ := by positivity
  have h5 : (((2 * Real.sqrt 2 / 3))⁻¹)⁻¹ ≤ (Real.exp ((1 : ℝ) / 18))⁻¹ :=
    (inv_le_inv₀ hbinv_pos hpos1).mpr h4
  rw [inv_inv] at h5
  exact h5

/-- BPP error amplification (one-sided form, finite): independent
votes each equal to `true` with probability at least `2 / 3` under
a product law on tuples (weight of a tuple is the product of the
per-vote probabilities, here with a common bias lower bound given
through a single PMF `p` on `Bool` with `p true ≥ 2 / 3`): the
majority is wrong (`false`) with probability at most
`exp (-(n / 18))` for `n ≥ 1`. The tuple law is the product PMF
built by recursion on the tuple as a function `Fin n → Bool`
weighted by `∏ i, (p (v i)).toReal`. -/
theorem bpp_majority_amplify {n : ℕ} (hn : 0 < n) (p : PMF Bool)
    (hp : (2 / 3 : ℝ) ≤ (p true).toReal) :
    (∑ v : Fin n → Bool, (∏ i, (p (v i)).toReal) *
      (if majority v = false then 1 else 0)) ≤ Real.exp (-(n / 18 : ℝ)) := by
  have _hn' := hn
  have hs_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have step1 : (∑ v : Fin n → Bool, (∏ i, (p (v i)).toReal) *
        (if majority v = false then 1 else 0))
        ≤ ∑ v : Fin n → Bool, (∏ i, (p (v i)).toReal) *
          Real.exp (Real.log 2 * ((n:ℝ)/2 - ∑ i : Fin n, (if v i = true then (1:ℝ) else 0))) := by
    apply Finset.sum_le_sum
    intro v _
    by_cases h : majority v = false
    · have hif : (if majority v = false then (1:ℝ) else 0) = 1 := by simp [h]
      rw [hif]
      have hw_nn : 0 ≤ ∏ i, (p (v i)).toReal := by
        apply Finset.prod_nonneg
        intro i _
        exact ENNReal.toReal_nonneg
      have h1 : (1:ℝ) ≤ Real.exp (Real.log 2 * ((n:ℝ)/2 - ∑ i : Fin n, (if v i = true then (1:ℝ) else 0))) := by
        apply Real.one_le_exp
        have hcard := bad_card_le n v h
        have hcount := card_true_eq n v
        have hle : ∑ i : Fin n, (if v i = true then (1:ℝ) else 0) ≤ (n:ℝ)/2 := by
          rw [← hcount]
          exact hcard
        have hnonneg : 0 ≤ (n:ℝ)/2 - ∑ i : Fin n, (if v i = true then (1:ℝ) else 0) := by linarith
        exact mul_nonneg (le_of_lt hs_pos) hnonneg
      calc (∏ i, (p (v i)).toReal) * 1 = ∏ i, (p (v i)).toReal := by ring
        _ ≤ (∏ i, (p (v i)).toReal) * Real.exp (Real.log 2 * ((n:ℝ)/2 - ∑ i : Fin n, (if v i = true then (1:ℝ) else 0))) :=
          le_mul_of_one_le_right hw_nn h1
    · have hif : (if majority v = false then (1:ℝ) else 0) = 0 := by simp [h]
      rw [hif]
      have hw_nn : 0 ≤ ∏ i, (p (v i)).toReal := by
        apply Finset.prod_nonneg
        intro i _
        exact ENNReal.toReal_nonneg
      have hexp_pos : 0 ≤ Real.exp (Real.log 2 * ((n:ℝ)/2 - ∑ i : Fin n, (if v i = true then (1:ℝ) else 0))) :=
        le_of_lt (Real.exp_pos _)
      calc (∏ i, (p (v i)).toReal) * 0 = 0 := by ring
        _ ≤ (∏ i, (p (v i)).toReal) * Real.exp (Real.log 2 * ((n:ℝ)/2 - ∑ i : Fin n, (if v i = true then (1:ℝ) else 0))) :=
          mul_nonneg hw_nn hexp_pos
  have hmgf_eq : ∀ v : Fin n → Bool,
      (∏ i, (p (v i)).toReal) * Real.exp (Real.log 2 * ((n:ℝ)/2 - ∑ i : Fin n, (if v i = true then (1:ℝ) else 0)))
        = ∏ i, ((p (v i)).toReal * Real.exp (Real.log 2 * (1/2 - (if v i = true then (1:ℝ) else 0)))) := by
    intro v
    have hexp : Real.exp (Real.log 2 * ((n:ℝ)/2 - ∑ i : Fin n, (if v i = true then (1:ℝ) else 0)))
        = ∏ i, Real.exp (Real.log 2 * (1/2 - (if v i = true then (1:ℝ) else 0))) := by
      rw [exp_split n v (Real.log 2)]
      rw [Real.exp_sum]
    rw [hexp]
    rw [← Finset.prod_mul_distrib]
  have step2 : (∑ v : Fin n → Bool, (∏ i, (p (v i)).toReal) *
        Real.exp (Real.log 2 * ((n:ℝ)/2 - ∑ i : Fin n, (if v i = true then (1:ℝ) else 0))))
      = ∏ i : Fin n, ∑ b : Bool, ((p b).toReal * Real.exp (Real.log 2 * (1/2 - (if b = true then (1:ℝ) else 0)))) := by
    have hsum : (∑ v : Fin n → Bool, (∏ i, (p (v i)).toReal) *
          Real.exp (Real.log 2 * ((n:ℝ)/2 - ∑ i : Fin n, (if v i = true then (1:ℝ) else 0))))
        = ∑ v : Fin n → Bool, ∏ i, (fun (_ : Fin n) (b : Bool) =>
            (p b).toReal * Real.exp (Real.log 2 * (1/2 - (if b = true then (1:ℝ) else 0)))) i (v i) := by
      apply Finset.sum_congr rfl
      intro v _
      exact hmgf_eq v
    rw [hsum]
    exact sum_pi_mul n (fun _ b =>
      (p b).toReal * Real.exp (Real.log 2 * (1/2 - (if b = true then (1:ℝ) else 0))))
  have hS_nn : 0 ≤ ∑ b : Bool, ((p b).toReal * Real.exp (Real.log 2 * (1/2 - (if b = true then (1:ℝ) else 0)))) := by
    apply Finset.sum_nonneg
    intro b _
    apply mul_nonneg ENNReal.toReal_nonneg
    exact le_of_lt (Real.exp_pos _)
  have hS_le : ∑ b : Bool, ((p b).toReal * Real.exp (Real.log 2 * (1/2 - (if b = true then (1:ℝ) else 0))))
      ≤ 2 * Real.sqrt 2 / 3 :=
    pervote_bound p hp
  have hprod_eq : (∏ _i : Fin n, ∑ b : Bool, ((p b).toReal * Real.exp (Real.log 2 * (1/2 - (if b = true then (1:ℝ) else 0)))))
      = (∑ b : Bool, ((p b).toReal * Real.exp (Real.log 2 * (1/2 - (if b = true then (1:ℝ) else 0))))) ^ n := by
    rw [Finset.prod_const]
    simp
  have hpow1 : (∏ i : Fin n, ∑ b : Bool, ((p b).toReal * Real.exp (Real.log 2 * (1/2 - (if b = true then (1:ℝ) else 0)))))
      ≤ (2 * Real.sqrt 2 / 3) ^ n := by
    rw [hprod_eq]
    exact pow_le_pow_left₀ hS_nn hS_le n
  have hpow2 : (2 * Real.sqrt 2 / 3) ^ n ≤ (Real.exp (-((1:ℝ)/18))) ^ n := by
    apply pow_le_pow_left₀ _ key_numeric n
    have hpos : (0:ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    positivity
  have hexp_pow : (Real.exp (-((1:ℝ)/18))) ^ n = Real.exp (-(n / 18 : ℝ)) := by
    have h : Real.exp ((n:ℝ) * (-((1:ℝ)/18))) = (Real.exp (-((1:ℝ)/18))) ^ n := by
      rw [Real.exp_nat_mul]
    have heq : (n:ℝ) * (-((1:ℝ)/18)) = -(n / 18 : ℝ) := by ring
    rw [heq] at h
    exact h.symm
  calc (∑ v : Fin n → Bool, (∏ i, (p (v i)).toReal) *
        (if majority v = false then 1 else 0))
        ≤ ∑ v : Fin n → Bool, (∏ i, (p (v i)).toReal) *
          Real.exp (Real.log 2 * ((n:ℝ)/2 - ∑ i : Fin n, (if v i = true then (1:ℝ) else 0))) := step1
      _ = ∏ i : Fin n, ∑ b : Bool, ((p b).toReal * Real.exp (Real.log 2 * (1/2 - (if b = true then (1:ℝ) else 0)))) := step2
      _ ≤ (2 * Real.sqrt 2 / 3) ^ n := hpow1
      _ ≤ (Real.exp (-((1:ℝ)/18))) ^ n := hpow2
      _ = Real.exp (-(n / 18 : ℝ)) := hexp_pow
