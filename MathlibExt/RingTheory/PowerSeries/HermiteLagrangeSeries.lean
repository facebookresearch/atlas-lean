/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.RingTheory.PowerSeries.Substitution
public import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

@[expose] public section

-- Author: @toskua, Avocado

namespace MetaMathlibExt

section
/-! # Hermite corollary of Lagrange inversion
-/

private lemma hli_constF (φ F : PowerSeries ℂ)
    (hφ : PowerSeries.coeff 0 φ ≠ 0)
    (hF : F * φ = PowerSeries.X) :
    PowerSeries.constantCoeff F = 0 := by
  have h := congrArg PowerSeries.constantCoeff hF
  rw [map_mul, PowerSeries.constantCoeff_X] at h
  rcases mul_eq_zero.mp h with h0 | h0
  · exact h0
  · exfalso; apply hφ; rw [PowerSeries.coeff_zero_eq_constantCoeff_apply]; exact h0

-- Setup: constCoeff ψ = 0
private lemma hli_constpsi (ψ F : PowerSeries ℂ)
    (hF0 : PowerSeries.constantCoeff F = 0)
    (hpsi2 : PowerSeries.subst F ψ = PowerSeries.X) :
    PowerSeries.constantCoeff ψ = 0 := by
  have h := PowerSeries.constantCoeff_subst_of_constantCoeff_zero hF0 ψ
  rw [hpsi2, Algebra.algebraMap_self, RingHom.id_apply] at h
  have hX : MvPowerSeries.constantCoeff (PowerSeries.X : PowerSeries ℂ) = 0 :=
      PowerSeries.constantCoeff_X
  rw [hX] at h
  exact h.symm

-- ψ = PowerSeries.X * (φ ∘ ψ)
private lemma hli_psi_eq (φ F ψ : PowerSeries ℂ)
    (hψ : PowerSeries.HasSubst ψ)
    (hF : F * φ = PowerSeries.X)
    (hpsi1 : PowerSeries.subst ψ F = PowerSeries.X) :
    ψ = PowerSeries.X * PowerSeries.subst ψ φ := by
  have h := congrArg (PowerSeries.subst ψ) hF
  rw [PowerSeries.subst_mul hψ, hpsi1, PowerSeries.subst_X hψ] at h
  exact h.symm

-- D * Φ + PowerSeries.X * A = 1
private lemma hli_chain (φ F ψ : PowerSeries ℂ)
    (hψ : PowerSeries.HasSubst ψ)
    (hF : F * φ = PowerSeries.X)
    (hpsi1 : PowerSeries.subst ψ F = PowerSeries.X) :
    PowerSeries.subst ψ (PowerSeries.derivative F) * PowerSeries.subst ψ φ +
      PowerSeries.X * PowerSeries.subst ψ (PowerSeries.derivative φ) = 1 := by
  have hL := PowerSeries.derivative.leibniz F φ
  rw [smul_eq_mul, smul_eq_mul] at hL
  have hderiv : F * PowerSeries.derivative φ + φ * PowerSeries.derivative F = 1 := by
    rw [← hL, hF, PowerSeries.derivative_X]
  have h1 : PowerSeries.subst ψ (1 : PowerSeries ℂ) = 1 := by
    rw [← PowerSeries.coe_substAlgHom hψ, map_one]
  have h := congrArg (PowerSeries.subst ψ) hderiv
  rw [PowerSeries.subst_add hψ, PowerSeries.subst_mul hψ, PowerSeries.subst_mul hψ, hpsi1, h1] at h
  linear_combination h

-- D * ψ' = 1
private lemma hli_Dpsi (F ψ : PowerSeries ℂ)
    (hψ : PowerSeries.HasSubst ψ)
    (hpsi1 : PowerSeries.subst ψ F = PowerSeries.X) :
    PowerSeries.subst ψ (PowerSeries.derivative F) * PowerSeries.derivative ψ = 1 := by
  have h := congrArg PowerSeries.derivative hpsi1
  rw [PowerSeries.derivative_subst hψ, PowerSeries.derivative_X] at h
  exact h

private lemma hli_Xmul0 (K : PowerSeries ℂ) : PowerSeries.coeff 0 (PowerSeries.X * K) = 0 := by
  rw [PowerSeries.coeff_mul, Finset.sum_eq_zero]
  intro p hp
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
  have h1 : p.1 = 0 := by omega
  simp [PowerSeries.coeff_X, h1]

private lemma hli_Xmul (K : PowerSeries ℂ) (n : ℕ) : PowerSeries.coeff (n + 1) (PowerSeries.X * K) =
    PowerSeries.coeff n K := by
  rw [PowerSeries.coeff_mul, Finset.sum_eq_single (1, n)]
  · simp [PowerSeries.coeff_X]
  · intro p hp hpn
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
    have h1 : p.1 ≠ 1 := by
      intro hcon
      apply hpn
      ext
      · simp_all
      · simp_all; omega
    simp [PowerSeries.coeff_X, h1]
  · intro hcon
    exfalso
    apply hcon
    rw [Finset.HasAntidiagonal.mem_antidiagonal]
    change (1 : ℕ) + n = n + 1
    omega

-- δ-lemma: PowerSeries.coeff r (v^(r+1) * (PowerSeries.X*u)') = δ_{r,0}, where v = u⁻¹
private lemma hli_delta (u : PowerSeries ℂ) (hu : PowerSeries.constantCoeff u ≠ 0) (r : ℕ) :
    PowerSeries.coeff r ((u⁻¹ ^ (r + 1)) * PowerSeries.derivative (PowerSeries.X * u)) =
      if r = 0 then 1 else 0 := by
  have hvu : u⁻¹ * u = 1 := PowerSeries.inv_mul_cancel u hu
  have huv : u * u⁻¹ = 1 := PowerSeries.mul_inv_cancel u hu
  -- PowerSeries.derivative of PowerSeries.X * u
  have hf : PowerSeries.derivative (PowerSeries.X * u) = u + PowerSeries.X * PowerSeries.derivative
      u := by
    have hL := PowerSeries.derivative.leibniz PowerSeries.X u
    rw [PowerSeries.derivative_X, smul_eq_mul, smul_eq_mul, mul_one, add_comm] at hL
    exact hL
  -- relation between derivatives from v * u = 1
  have hL2 := PowerSeries.derivative.leibniz (u⁻¹) u
  rw [smul_eq_mul, smul_eq_mul, hvu, PowerSeries.derivative_one] at hL2
  have hrel : u⁻¹ * PowerSeries.derivative u + PowerSeries.derivative (u⁻¹) * u = 0 := by
    linear_combination -hL2
  -- expansion
  have hvr : u⁻¹ ^ (r + 1) * u = u⁻¹ ^ r := by
    rw [pow_succ, mul_assoc, hvu, mul_one]
  have hexpand : (u⁻¹ ^ (r + 1)) * PowerSeries.derivative (PowerSeries.X * u)
      = u⁻¹ ^ r + PowerSeries.X * (u⁻¹ ^ (r + 1) * PowerSeries.derivative u) := by
    rw [hf]
    linear_combination hvr
  rw [hexpand, map_add]
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · rw [hli_Xmul0, add_zero, pow_zero, PowerSeries.coeff_one]
  · obtain ⟨s, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt hr)
    rw [hli_Xmul, ite_eq_right (Nat.succ_ne_zero s)]
    -- goal: PowerSeries.coeff (s+1) v^{s+1} + PowerSeries.coeff s (v^{s+2} * u') = 0
    have e1 : u⁻¹ * PowerSeries.derivative u = -(PowerSeries.derivative (u⁻¹) * u) :=
      eq_neg_of_add_eq_zero_left hrel
    have hvr2 : u⁻¹ ^ (s + 1) * u = u⁻¹ ^ s := by
      rw [pow_succ, mul_assoc, hvu, mul_one]
    have h3 : u⁻¹ ^ (s + 1) * (PowerSeries.derivative (u⁻¹) * u)
        = u⁻¹ ^ s * PowerSeries.derivative (u⁻¹) := by
      have h4 : u⁻¹ ^ (s + 1) * (PowerSeries.derivative (u⁻¹) * u)
          = (u⁻¹ ^ (s + 1) * u) * PowerSeries.derivative (u⁻¹) := by ring
      rw [h4, hvr2]
    have hstep : u⁻¹ ^ (s + 2) * PowerSeries.derivative u
        = -(u⁻¹ ^ s * PowerSeries.derivative (u⁻¹)) := by
      have h2 : u⁻¹ ^ (s + 2) * PowerSeries.derivative u
          = u⁻¹ ^ (s + 1) * (u⁻¹ * PowerSeries.derivative u) := by ring
      rw [h2, e1, mul_neg, h3]
    -- the (PowerSeries.X * v^{s+1})' trick
    have hD : PowerSeries.derivative (PowerSeries.X * u⁻¹ ^ (s + 1))
        = u⁻¹ ^ (s + 1) + PowerSeries.X *
            (PowerSeries.C ((s + 1 : ℕ) : ℂ) * (u⁻¹ ^ s * PowerSeries.derivative (u⁻¹))) := by
      have hL := PowerSeries.derivative.leibniz PowerSeries.X (u⁻¹ ^ (s + 1))
      rw [PowerSeries.derivative_X, PowerSeries.derivative_pow, Nat.add_sub_cancel] at hL
      rw [smul_eq_mul, smul_eq_mul, mul_one] at hL
      have hC : ((s + 1 : ℕ) : PowerSeries ℂ) = PowerSeries.C ((s + 1 : ℕ) : ℂ) :=
        (map_natCast _ _).symm
      rw [hC] at hL
      linear_combination hL
    have hDc := congrArg (PowerSeries.coeff (s + 1)) hD
    rw [PowerSeries.coeff_derivative, hli_Xmul, map_add, hli_Xmul, PowerSeries.coeff_C_mul] at hDc
    have hcancel : ((s + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero s
    have heq : PowerSeries.coeff (s + 1) (u⁻¹ ^ (s + 1))
        = PowerSeries.coeff s (u⁻¹ ^ s * PowerSeries.derivative (u⁻¹)) := by
      have hlin : ((s + 1 : ℕ) : ℂ) * PowerSeries.coeff (s + 1) (u⁻¹ ^ (s + 1))
          = ((s + 1 : ℕ) : ℂ) * PowerSeries.coeff s (u⁻¹ ^ s * PowerSeries.derivative (u⁻¹)) := by
        linear_combination hDc
      exact mul_left_cancel₀ hcancel hlin
    rw [hstep, map_neg, heq, add_neg_cancel]


-- vanishing of ψ^d coefficients below d
private lemma hli_psi_pow_coeff (ψ : PowerSeries ℂ) (hψ0 : PowerSeries.constantCoeff ψ = 0)
    (d b : ℕ) (h : b < d) : PowerSeries.coeff b (ψ ^ d) = 0 := by
  apply PowerSeries.coeff_of_lt_order
  calc (↑b : ℕ∞) < ↑d := by exact_mod_cast h
    _ ≤ (ψ ^ d).order := PowerSeries.le_order_pow_of_constantCoeff_eq_zero d hψ0

-- PowerSeries.coeff of PowerSeries.X^d * K
private lemma hli_Xpow_mul (d N : ℕ) (K : PowerSeries ℂ) :
    PowerSeries.coeff N (PowerSeries.X ^ d * K) = if d ≤ N then PowerSeries.coeff (N - d) K else
        0 := by
  by_cases h : d ≤ N
  · rw [PowerSeries.coeff_mul, Finset.sum_eq_single (d, N - d)]
    · rw [PowerSeries.coeff_X_pow, ite_eq_left rfl, one_mul, ite_eq_left h]
    · intro p hp hpn
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
      have hne : p.1 ≠ d := by
        intro hcon
        apply hpn
        ext
        · simp_all
        · simp_all; omega
      simp [PowerSeries.coeff_X_pow, hne]
    · intro hcon
      exfalso
      apply hcon
      rw [Finset.HasAntidiagonal.mem_antidiagonal]
      change d + (N - d) = N
      omega
  · rw [ite_eq_right h, PowerSeries.coeff_mul, Finset.sum_eq_zero]
    intro p hp
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
    have hne : p.1 ≠ d := by omega
    simp [PowerSeries.coeff_X_pow, hne]

private lemma hli_psipow (ψ Φ : PowerSeries ℂ) (hψeq : ψ = PowerSeries.X * Φ) (d : ℕ) :
    ψ ^ d = PowerSeries.X ^ d * Φ ^ d := by
  rw [hψeq, mul_pow]

-- inner δ computation
private lemma hli_inner (ψ Φ : PowerSeries ℂ) (hψeq : ψ = PowerSeries.X * Φ)
    (hΦ0 : PowerSeries.constantCoeff Φ ≠ 0) (d N : ℕ) :
    PowerSeries.coeff N ((Φ⁻¹ ^ (N + 1)) * ψ ^ d * PowerSeries.derivative ψ) =
      if d = N then 1 else 0 := by
  rw [hli_psipow ψ Φ hψeq d]
  have hrew : (Φ⁻¹ ^ (N + 1)) * (PowerSeries.X ^ d * Φ ^ d) * PowerSeries.derivative ψ
      = PowerSeries.X ^ d * ((Φ⁻¹ ^ (N + 1) * Φ ^ d) * PowerSeries.derivative ψ) := by ring
  rw [hrew, hli_Xpow_mul]
  by_cases h : d ≤ N
  · rw [ite_eq_left h]
    have h2 : Φ⁻¹ ^ d * Φ ^ d = 1 := by
      rw [← mul_pow, PowerSeries.inv_mul_cancel _ hΦ0, one_pow]
    have h1 : Φ⁻¹ ^ (N + 1) = Φ⁻¹ ^ (N - d + 1) * Φ⁻¹ ^ d := by
      rw [← pow_add]; congr 1; omega
    have hexp : Φ⁻¹ ^ (N + 1) * Φ ^ d = Φ⁻¹ ^ (N - d + 1) := by
      rw [h1, mul_assoc, h2, mul_one]
    rw [hexp]
    have hdel := hli_delta Φ hΦ0 (N - d)
    rw [← hψeq] at hdel
    rw [hdel]
    by_cases h' : d = N
    · subst h'; simp
    · rw [ite_eq_right h']
      have hne : N - d ≠ 0 := by omega
      rw [ite_eq_right hne]
  · rw [ite_eq_right h]
    have hne : d ≠ N := by omega
    rw [ite_eq_right hne]

-- finite expansion of PowerSeries.subst coeffs
private lemma hli_B (ψ S : PowerSeries ℂ)
    (hψ : PowerSeries.HasSubst ψ) (hψ0 : PowerSeries.constantCoeff ψ = 0)
    (b N : ℕ) (hb : b ≤ N) :
    PowerSeries.coeff b (PowerSeries.subst ψ S)
      = ∑ d ∈ Finset.range (N + 1), PowerSeries.coeff d S * PowerSeries.coeff b (ψ ^ d) := by
  trans ∑ d ∈ Finset.range (b + 1), PowerSeries.coeff d S • PowerSeries.coeff b (ψ ^ d)
  · rw [PowerSeries.coeff_subst' hψ S b]
    apply finsum_eq_sum_of_support_subset
    intro d hd
    rw [Function.mem_support] at hd
    rw [Finset.coe_range, Set.mem_Iio]
    by_contra hcon
    have hle : b + 1 ≤ d := not_lt.mp hcon
    apply hd
    change PowerSeries.coeff d S • PowerSeries.coeff b (ψ ^ d) = 0
    rw [hli_psi_pow_coeff ψ hψ0 d b (by omega), smul_zero]
  · trans ∑ d ∈ Finset.range (N + 1), PowerSeries.coeff d S • PowerSeries.coeff b (ψ ^ d)
    · apply Finset.sum_subset (Finset.range_mono (by omega : b + 1 ≤ N + 1))
      intro d hd1 hd2
      rw [Finset.mem_range] at hd2
      simp at hd2
      rw [smul_eq_mul, hli_psi_pow_coeff ψ hψ0 d b (by omega), mul_zero]
    · apply Finset.sum_congr rfl
      intro d _
      rw [smul_eq_mul]

-- double sum swap
private lemma hli_BC (ψ S : PowerSeries ℂ)
    (hψ : PowerSeries.HasSubst ψ) (hψ0 : PowerSeries.constantCoeff ψ = 0)
    (N bc : ℕ) (hbc : bc ≤ N) :
    PowerSeries.coeff bc (PowerSeries.subst ψ S * PowerSeries.derivative ψ)
      = ∑ d ∈ Finset.range (N + 1),
        PowerSeries.coeff d S * PowerSeries.coeff bc (ψ ^ d * PowerSeries.derivative ψ) := by
  trans ∑ q ∈ Finset.HasAntidiagonal.antidiagonal bc,
    ∑ d ∈ Finset.range (N + 1),
      PowerSeries.coeff d S * (PowerSeries.coeff q.1 (ψ ^ d) * PowerSeries.coeff q.2
          (PowerSeries.derivative ψ))
  · rw [PowerSeries.coeff_mul]
    apply Finset.sum_congr rfl
    intro q hq
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hq
    have hB := hli_B ψ S hψ hψ0 q.1 N (by omega)
    rw [hB, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro d _
    ring
  · rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro d _
    rw [← Finset.mul_sum]
    congr 1
    rw [← PowerSeries.coeff_mul]

-- outer Fubini
private lemma hli_M (ψ S : PowerSeries ℂ)
    (hψ : PowerSeries.HasSubst ψ) (hψ0 : PowerSeries.constantCoeff ψ = 0)
    (A : PowerSeries ℂ) (N : ℕ) :
    PowerSeries.coeff N (A * (PowerSeries.subst ψ S * PowerSeries.derivative ψ))
      = ∑ d ∈ Finset.range (N + 1),
        PowerSeries.coeff d S * PowerSeries.coeff N (A * ψ ^ d * PowerSeries.derivative ψ) := by
  trans ∑ p ∈ Finset.HasAntidiagonal.antidiagonal N,
    ∑ d ∈ Finset.range (N + 1),
      PowerSeries.coeff d S * (PowerSeries.coeff p.1 A * PowerSeries.coeff p.2
          (ψ ^ d * PowerSeries.derivative ψ))
  · rw [PowerSeries.coeff_mul]
    apply Finset.sum_congr rfl
    intro p hp
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
    rw [hli_BC ψ S hψ hψ0 N p.2 (by omega), Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d _
    ring
  · rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro d _
    rw [← Finset.mul_sum]
    congr 1
    rw [show A * ψ ^ d * PowerSeries.derivative ψ = A * (ψ ^ d * PowerSeries.derivative ψ) from
      mul_assoc _ _ _, ← PowerSeries.coeff_mul]

-- level identity
private lemma hli_level (g φ ψ Φ : PowerSeries ℂ)
    (hψ : PowerSeries.HasSubst ψ) (hψ0 : PowerSeries.constantCoeff ψ = 0)
    (hΦ : Φ = PowerSeries.subst ψ φ) (hψeq : ψ = PowerSeries.X * Φ)
    (hΦ0 : PowerSeries.constantCoeff Φ ≠ 0) (N : ℕ) :
    PowerSeries.coeff N (PowerSeries.mk fun n => PowerSeries.coeff n (g * φ ^ n))
      = PowerSeries.coeff N (PowerSeries.subst ψ g * (PowerSeries.derivative ψ * Φ⁻¹)) := by
  simp only [PowerSeries.coeff_mk]
  have hS : PowerSeries.subst ψ (g * φ ^ N) = PowerSeries.subst ψ g * Φ ^ N := by
    rw [PowerSeries.subst_mul hψ, PowerSeries.subst_pow hψ, ← hΦ]
  have hΦN : Φ⁻¹ ^ N * Φ ^ N = 1 := by
    rw [← mul_pow, PowerSeries.inv_mul_cancel _ hΦ0, one_pow]
  have hM : (Φ⁻¹ ^ (N + 1)) * PowerSeries.subst ψ (g * φ ^ N) * PowerSeries.derivative ψ
      = PowerSeries.subst ψ g * (PowerSeries.derivative ψ * Φ⁻¹) := by
    rw [hS]
    have h1 : Φ⁻¹ ^ (N + 1) = Φ⁻¹ * Φ⁻¹ ^ N := by rw [pow_succ']
    calc (Φ⁻¹ ^ (N + 1)) * (PowerSeries.subst ψ g * Φ ^ N) * PowerSeries.derivative ψ
        = PowerSeries.subst ψ g * PowerSeries.derivative ψ * (Φ⁻¹ ^ (N + 1) * Φ ^ N) := by ring
      _ = PowerSeries.subst ψ g * PowerSeries.derivative ψ * Φ⁻¹ := by
          rw [h1, show Φ⁻¹ * Φ⁻¹ ^ N * Φ ^ N = Φ⁻¹ from by
            rw [mul_assoc, hΦN, mul_one]]
      _ = PowerSeries.subst ψ g * (PowerSeries.derivative ψ * Φ⁻¹) := by ring
  have hsum : PowerSeries.coeff N (g * φ ^ N)
      = ∑ d ∈ Finset.range (N + 1),
        PowerSeries.coeff d (g * φ ^ N) * PowerSeries.coeff N
            ((Φ⁻¹ ^ (N + 1)) * ψ ^ d * PowerSeries.derivative ψ) := by
    trans ∑ d ∈ Finset.range (N + 1), if d = N then PowerSeries.coeff d (g * φ ^ N) else 0
    · rw [Finset.sum_ite_eq' _ N (fun d => PowerSeries.coeff d (g * φ ^ N)),
        ite_eq_left (Finset.mem_range.mpr (Nat.lt_succ_self N))]
    · apply Finset.sum_congr rfl
      intro d _
      rw [hli_inner ψ Φ hψeq hΦ0 d N, mul_ite, mul_one, mul_zero]
  have hsum2 : PowerSeries.coeff N (PowerSeries.subst ψ g * (PowerSeries.derivative ψ * Φ⁻¹))
      = ∑ d ∈ Finset.range (N + 1),
        PowerSeries.coeff d (g * φ ^ N) * PowerSeries.coeff N
            ((Φ⁻¹ ^ (N + 1)) * ψ ^ d * PowerSeries.derivative ψ) := by
    rw [← hM, mul_assoc]
    exact hli_M ψ (g * φ ^ N) hψ hψ0 (Φ⁻¹ ^ (N + 1)) N
  rw [hsum, hsum2]


-- H * E = g∘ψ
private lemma hli_HE (g φ ψ Φ D A : PowerSeries ℂ)
    (hψ : PowerSeries.HasSubst ψ) (hψ0 : PowerSeries.constantCoeff ψ = 0)
    (hΦ : Φ = PowerSeries.subst ψ φ) (hψeq : ψ = PowerSeries.X * Φ)
    (hΦ0 : PowerSeries.constantCoeff Φ ≠ 0)
    (hchain : D * Φ + PowerSeries.X * A = 1)
    (hDpsi : D * PowerSeries.derivative ψ = 1) :
    (PowerSeries.mk fun n => PowerSeries.coeff n (g * φ ^ n)) * (1 - PowerSeries.X * A) =
        PowerSeries.subst ψ g := by
  have hEc : PowerSeries.constantCoeff (1 - PowerSeries.X * A) ≠ 0 := by
    have h1 : PowerSeries.constantCoeff (1 - PowerSeries.X * A) = 1 := by simp
    rw [h1]
    exact one_ne_zero
  have hED : (1 - PowerSeries.X * A) = D * Φ := by linear_combination -hchain
  have hprod : (1 - PowerSeries.X * A) * (PowerSeries.derivative ψ * Φ⁻¹) = 1 := by
    have h1 : Φ * Φ⁻¹ = 1 := PowerSeries.mul_inv_cancel Φ hΦ0
    rw [hED]
    calc D * Φ * (PowerSeries.derivative ψ * Φ⁻¹)
        = (D * PowerSeries.derivative ψ) * (Φ * Φ⁻¹) := by ring
      _ = 1 := by rw [hDpsi, h1, mul_one]
  have hEinv : (1 - PowerSeries.X * A)⁻¹ = PowerSeries.derivative ψ * Φ⁻¹ :=
    ((PowerSeries.eq_inv_iff_mul_eq_one hEc).mpr (by rw [mul_comm]; exact hprod)).symm
  have hH : (PowerSeries.mk fun n => PowerSeries.coeff n (g * φ ^ n)) = PowerSeries.subst ψ g *
      (1 - PowerSeries.X * A)⁻¹ := by
    apply PowerSeries.ext
    intro N
    rw [hEinv]
    exact hli_level g φ ψ Φ hψ hψ0 hΦ hψeq hΦ0 N
  rw [hH, mul_assoc, PowerSeries.inv_mul_cancel _ hEc, mul_one]

/--
**Hermite's form of Lagrange inversion as a series identity.** Let $\varphi$, $g$, $F$ and $\psi$
be formal power series over $\mathbb{C}$, write $F'$ for the formal derivative of $F$, and write
$h(k)$ for the substitution of a power series $k$ into a power series $h$. Suppose that $\varphi$
has nonzero constant term, that $F\varphi = X$, and that $\psi$ is a two-sided compositional
inverse of $F$, that is, $F(\psi) = X$ and $\psi(F) = X$. Let $H = \sum_{n \ge 0} c_n X^n$,
where $c_n$ is the coefficient of $X^n$ in $g\varphi^n$. Then

$$X\, g(\psi) = H\, \psi\, F'(\psi).$$

The source states this, with $F = X/\varphi$, as $X\, g(\psi) / (\psi\, F'(\psi)) = H$; the
form here is cleared of denominators.

Proves `Wanted` entry `hermite_lagrange_inversion`.

Source: Bakir Farhi, "Some Applications of the Lagrange Inversion Formula
for the k-Fibonacci Numbers," Journal of Integer Sequences 27 (2024),
Article 24.1.1, Corollary (Hermite, label t-her), lines 205–210,
https://cs.uwaterloo.ca/journals/JIS/VOL27/Farhi/farhi35.tex
-/
theorem hermite_lagrange_inversion
    (φ g F ψ : PowerSeries ℂ)
    (hφ : PowerSeries.coeff 0 φ ≠ 0)
    (hF : F * φ = PowerSeries.X)
    (hpsi1 : PowerSeries.subst ψ F = PowerSeries.X)
    (hpsi2 : PowerSeries.subst F ψ = PowerSeries.X) :
    PowerSeries.X * PowerSeries.subst ψ g =
      (PowerSeries.mk (fun n : ℕ => PowerSeries.coeff n (g * φ ^ n)) :
        PowerSeries ℂ) * ψ *
        PowerSeries.subst ψ (PowerSeries.derivative F) := by
  have hφ0 : PowerSeries.constantCoeff φ ≠ 0 := by
    intro hc
    apply hφ
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, hc]
  have hF0 : PowerSeries.constantCoeff F = 0 := hli_constF φ F hφ hF
  have hψ0 : PowerSeries.constantCoeff ψ = 0 := hli_constpsi ψ F hF0 hpsi2
  have hψ : PowerSeries.HasSubst ψ := PowerSeries.HasSubst.of_constantCoeff_zero' hψ0
  have hψeq : ψ = PowerSeries.X * PowerSeries.subst ψ φ := hli_psi_eq φ F ψ hψ hF hpsi1
  have hΦ0 : PowerSeries.constantCoeff (PowerSeries.subst ψ φ) ≠ 0 := by
    have h := PowerSeries.constantCoeff_subst_of_constantCoeff_zero hψ0 φ
    rw [Algebra.algebraMap_self, RingHom.id_apply] at h
    rw [PowerSeries.constantCoeff_eq, h]
    exact hφ0
  have hchain := hli_chain φ F ψ hψ hF hpsi1
  have hDpsi := hli_Dpsi F ψ hψ hpsi1
  have hHE := hli_HE g φ ψ (PowerSeries.subst ψ φ) (PowerSeries.subst ψ (PowerSeries.derivative F))
    (PowerSeries.subst ψ (PowerSeries.derivative φ)) hψ hψ0 rfl hψeq hΦ0 hchain hDpsi
  have hXE : PowerSeries.X * (1 - PowerSeries.X * PowerSeries.subst ψ (PowerSeries.derivative φ))
      = ψ * PowerSeries.subst ψ (PowerSeries.derivative F) := by
    linear_combination (-PowerSeries.X) * hchain - (PowerSeries.subst ψ (PowerSeries.derivative F))
        * hψeq
  have step1 : PowerSeries.X * PowerSeries.subst ψ g
      = (PowerSeries.mk fun n => PowerSeries.coeff n (g * φ ^ n)) *
          (PowerSeries.X * (1 - PowerSeries.X * PowerSeries.subst ψ
              (PowerSeries.derivative φ))) := by
    rw [← hHE]; ring
  rw [step1, hXE, mul_assoc]

end

end MetaMathlibExt
