/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.OrdinaryHypergeometric
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

@[expose] public section

/-!
# Gauss summation specialized to Frisch's binomial identity
-/

open Finset Filter Topology

namespace MetaMathlibExt

section

private theorem poch_prod (s : ℝ) (k : ℕ) :
    (ascPochhammer ℝ (k + 1)).eval s = ∏ j ∈ Finset.range (k + 1), (s + (j : ℝ)) := by
  induction k with
  | zero =>
    rw [Finset.prod_range_succ, Finset.range_zero, Finset.prod_empty]
    simp [ascPochhammer_one]
  | succ k ih =>
    have hcast : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
    have h1 : (ascPochhammer ℝ (k + 1 + 1)).eval s
        = (ascPochhammer ℝ (k + 1)).eval s * (s + ((k + 1 : ℕ) : ℝ)) :=
      ascPochhammer_succ_eval (k + 1) s
    rw [h1, ih, hcast]
    conv_rhs => rw [Finset.prod_range_succ, hcast]

private theorem poch_one (k : ℕ) :
    (ascPochhammer ℝ k).eval (1 : ℝ) = (Nat.factorial k : ℝ) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [ascPochhammer_succ_eval, ih]
    rw [Nat.factorial_succ]
    push_cast
    ring

private theorem poch_ratio (m k : ℕ) (hm : 1 ≤ m) :
    (ascPochhammer ℝ k).eval (((m + 1 : ℕ)) : ℝ)
      = (((m : ℝ) + (k : ℝ)) / (m : ℝ)) * (ascPochhammer ℝ k).eval (m : ℝ) := by
  have hm0 : (m : ℝ) ≠ 0 := by
    have : (0 : ℝ) < (m : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (by omega)
    exact ne_of_gt this
  induction k with
  | zero => simp [hm0]
  | succ k ih =>
    rw [ascPochhammer_succ_eval, ascPochhammer_succ_eval, ih]
    push_cast
    field_simp
    ring

private theorem poch_nat_le (m k : ℕ) (hm : 1 ≤ m) :
    (ascPochhammer ℝ k).eval (m : ℝ) / (Nat.factorial k : ℝ)
      ≤ ((k : ℝ) + 1) ^ ((m : ℝ) - 1) := by
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
  suffices h : ∀ p : ℕ, 1 ≤ p →
      (ascPochhammer ℝ k).eval (p : ℝ) / (Nat.factorial k : ℝ)
        ≤ ((k : ℝ) + 1) ^ ((p : ℝ) - 1) from h m hm
  intro p
  induction p with
  | zero => intro hcon; omega
  | succ p ih =>
    intro hp1
    by_cases hp0 : p = 0
    · subst hp0
      have h1 : ((((0 + 1 : ℕ))) : ℝ) = (1 : ℝ) := by norm_cast
      rw [h1, poch_one]
      have hfact : (Nat.factorial k : ℝ) ≠ 0 :=
        Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
      rw [div_self hfact]
      simp
    · have hpp : 1 ≤ p := by omega
      have ih' := ih hpp
      have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 0 < p)
      have hpos : 0 < (ascPochhammer ℝ k).eval (p : ℝ) := by
        apply ascPochhammer_pos
        exact_mod_cast (by omega : 0 < p)
      have hfactpos : (0 : ℝ) < (Nat.factorial k : ℝ) := by
        exact_mod_cast Nat.factorial_pos k
      have hY0 : (0 : ℝ) ≤ (ascPochhammer ℝ k).eval (p : ℝ) / (Nat.factorial k : ℝ) :=
        div_nonneg hpos.le hfactpos.le
      have hk1pos : (0 : ℝ) < (k : ℝ) + 1 := by
        have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
        linarith
      have hstep : ((p : ℝ) + (k : ℝ)) / (p : ℝ) ≤ (k : ℝ) + 1 := by
        have hmk : (k : ℝ) ≤ (p : ℝ) * (k : ℝ) := by
          have hp1R : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp
          calc (k : ℝ) = 1 * (k : ℝ) := by ring
            _ ≤ (p : ℝ) * (k : ℝ) :=
              mul_le_mul_of_nonneg_right hp1R (Nat.cast_nonneg k)
        rw [div_le_iff₀ hpR]
        linarith
      have hexp : ((((p + 1 : ℕ))) : ℝ) - 1 = ((p : ℝ) - 1) + 1 := by
        push_cast; ring
      have hpcast : ((((p + 1 : ℕ))) : ℝ) = (p : ℝ) + 1 := by push_cast; ring
      have hrat := poch_ratio p k (by omega : 1 ≤ p)
      have hrw : (ascPochhammer ℝ k).eval (((p + 1 : ℕ) : ℝ)) / (Nat.factorial k : ℝ)
          = (((p : ℝ) + (k : ℝ)) / (p : ℝ))
            * ((ascPochhammer ℝ k).eval (p : ℝ) / (Nat.factorial k : ℝ)) := by
        rw [hpcast] at hrat ⊢
        rw [hrat]; ring
      rw [hrw, hexp, Real.rpow_add hk1pos]
      simp only [Real.rpow_one]
      calc (((p : ℝ) + (k : ℝ)) / (p : ℝ))
            * ((ascPochhammer ℝ k).eval (p : ℝ) / (Nat.factorial k : ℝ))
          ≤ ((k : ℝ) + 1) * ((ascPochhammer ℝ k).eval (p : ℝ) / (Nat.factorial k : ℝ)) :=
            mul_le_mul_of_nonneg_right hstep hY0
        _ ≤ ((k : ℝ) + 1) * (((k : ℝ) + 1) ^ ((p : ℝ) - 1)) :=
            mul_le_mul_of_nonneg_left ih' hk1pos.le
        _ = ((k : ℝ) + 1) ^ ((p : ℝ) - 1) * ((k : ℝ) + 1) := by ring

private theorem poch_ratio_rpow_bound (A C c : ℝ) (hA : A = C - c) (hC : 0 < C) (_hc : 0 < c) :
    ∃ M : ℝ, 0 < M ∧ ∀ᶠ k : ℕ in atTop,
      |(ascPochhammer ℝ (k + 1)).eval A / (ascPochhammer ℝ (k + 1)).eval C|
        ≤ M * (k : ℝ) ^ (-c) := by
  have hCpos : ∀ k : ℕ, 0 < (ascPochhammer ℝ k).eval C :=
    fun k => ascPochhammer_pos k C hC
  by_cases hdeg : ∃ m0 : ℕ, A = -((m0 : ℕ) : ℝ)
  · obtain ⟨m0, hm0⟩ := hdeg
    refine ⟨1, one_pos, ?_⟩
    filter_upwards [eventually_ge_atTop m0] with k hk
    have hzero : (ascPochhammer ℝ (k + 1)).eval A = 0 := by
      rw [ascPochhammer_eval_eq_zero_iff]
      refine ⟨m0, by omega, by linarith⟩
    rw [hzero, zero_div, abs_zero]
    apply mul_nonneg zero_le_one
    exact Real.rpow_nonneg (Nat.cast_nonneg k) _
  · rw [not_exists] at hdeg
    have hGA : Real.Gamma A ≠ 0 := by
      apply Real.Gamma_ne_zero
      intro m
      exact hdeg m
    have hGC : Real.Gamma C ≠ 0 := ne_of_gt (Real.Gamma_pos_of_pos hC)
    have hlimC : Tendsto (Real.GammaSeq C) atTop (𝓝 (Real.Gamma C)) :=
      Real.GammaSeq_tendsto_Gamma C
    have hlimA : Tendsto (Real.GammaSeq A) atTop (𝓝 (Real.Gamma A)) :=
      Real.GammaSeq_tendsto_Gamma A
    have hlim : Tendsto (fun k : ℕ => Real.GammaSeq C k / Real.GammaSeq A k)
        atTop (𝓝 (Real.Gamma C / Real.Gamma A)) :=
      hlimC.div hlimA hGA
    refine ⟨‖Real.Gamma C / Real.Gamma A‖ + 1, by positivity, ?_⟩
    have hball := Metric.ball_mem_nhds (Real.Gamma C / Real.Gamma A) one_pos
    have hev0 := hlim.eventually hball
    have hGS : ∀ (s : ℝ) (k : ℕ), Real.GammaSeq s k
        = (k : ℝ) ^ s * (Nat.factorial k : ℝ) / (ascPochhammer ℝ (k + 1)).eval s := by
      intro s k
      unfold Real.GammaSeq
      rw [poch_prod]
    have hCeq : C = c + A := by linarith
    filter_upwards [eventually_ge_atTop 1, hev0] with k hk hmem
    have hkR : (0 : ℝ) < (k : ℝ) := by
      have : 0 < k := by omega
      exact_mod_cast this
    have hCk1 : (ascPochhammer ℝ (k + 1)).eval C ≠ 0 :=
      ne_of_gt (hCpos (k + 1))
    have hAk1 : (ascPochhammer ℝ (k + 1)).eval A ≠ 0 := by
      intro hcon
      rw [ascPochhammer_eval_eq_zero_iff] at hcon
      obtain ⟨j, _, hjA⟩ := hcon
      exact hdeg j (by linarith)
    have hfact : (Nat.factorial k : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
    have hrA : (k : ℝ) ^ A ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hkR A)
    have hrC : (k : ℝ) ^ C ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hkR C)
    have hdist : dist (Real.GammaSeq C k / Real.GammaSeq A k)
        (Real.Gamma C / Real.Gamma A) < 1 := Metric.mem_ball.mp hmem
    have htri : ‖Real.GammaSeq C k / Real.GammaSeq A k‖
        ≤ ‖Real.Gamma C / Real.Gamma A‖ + 1 := by
      have h1 : ‖Real.GammaSeq C k / Real.GammaSeq A k‖
          ≤ ‖Real.GammaSeq C k / Real.GammaSeq A k - Real.Gamma C / Real.Gamma A‖
            + ‖Real.Gamma C / Real.Gamma A‖ := by
        have hle := norm_add_le
          (Real.GammaSeq C k / Real.GammaSeq A k - Real.Gamma C / Real.Gamma A)
          (Real.Gamma C / Real.Gamma A)
        rwa [sub_add_cancel] at hle
      have h2 : ‖Real.GammaSeq C k / Real.GammaSeq A k - Real.Gamma C / Real.Gamma A‖ < 1 := by
        rwa [← dist_eq_norm]
      linarith
    have hkc : (k : ℝ) ^ (-c) * (k : ℝ) ^ c = 1 := by
      rw [← Real.rpow_add hkR]
      simp
    have hratio : (ascPochhammer ℝ (k + 1)).eval A / (ascPochhammer ℝ (k + 1)).eval C
        = (k : ℝ) ^ (-c) * (Real.GammaSeq C k / Real.GammaSeq A k) := by
      rw [hGS C k, hGS A k, hCeq, Real.rpow_add hkR]
      field_simp
      rw [hkc]
    rw [hratio, abs_mul, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg k) _)]
    have hnorm : |(Real.GammaSeq C k / Real.GammaSeq A k)|
        = ‖Real.GammaSeq C k / Real.GammaSeq A k‖ := (Real.norm_eq_abs _).symm
    rw [hnorm]
    calc (k : ℝ) ^ (-c) * ‖Real.GammaSeq C k / Real.GammaSeq A k‖
        ≤ (k : ℝ) ^ (-c) * (‖Real.Gamma C / Real.Gamma A‖ + 1) :=
          mul_le_mul_of_nonneg_left htri
            (Real.rpow_nonneg (Nat.cast_nonneg k) _)
      _ = (‖Real.Gamma C / Real.Gamma A‖ + 1) * (k : ℝ) ^ (-c) := by ring

private noncomputable def tterm (A C β : ℝ) (k : ℕ) : ℝ :=
  (ascPochhammer ℝ k).eval A * (ascPochhammer ℝ k).eval β /
    ((ascPochhammer ℝ k).eval C * (Nat.factorial k : ℝ))

private noncomputable def vterm (A C β : ℝ) : ℕ → ℝ
  | 0 => 0
  | k + 1 => (ascPochhammer ℝ (k + 1)).eval A * (ascPochhammer ℝ k).eval (β + 1) /
    ((ascPochhammer ℝ k).eval C * (Nat.factorial k : ℝ))

-- helper: (k-1 : ℝ) comparisons for k ≥ 2
private theorem rpow_neg_sub_le (k : ℕ) (hk : 2 ≤ k) (c : ℝ) (hc : 0 < c) :
    ((k : ℝ) - 1) ^ (-c) ≤ 2 ^ c * (k : ℝ) ^ (-c) := by
  have hkR : (0 : ℝ) < (k : ℝ) := by
    have : 0 < k := by omega
    exact_mod_cast this
  have h2R : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hkm : (0 : ℝ) < (k : ℝ) - 1 := by linarith
  have hle : (k : ℝ) / 2 ≤ (k : ℝ) -
      1 := by linarith [hkR, show (2:ℝ) ≤ (k:ℝ) from by exact_mod_cast hk]
  have h3 : ((k : ℝ) / 2) ^ c ≤ ((k : ℝ) - 1) ^ c :=
    Real.rpow_le_rpow (by positivity) hle hc.le
  have h4 : ((k : ℝ) - 1) ^ (-c) ≤ ((k : ℝ) / 2) ^ (-c) := by
    rw [Real.rpow_neg hkm.le, Real.rpow_neg (by positivity : (0:ℝ) ≤ (k:ℝ)/2)]
    rw [← one_div, ← one_div]
    exact one_div_le_one_div_of_le (Real.rpow_pos_of_pos (by positivity : (0:ℝ) < (k:ℝ)/2) _) h3
  have h5 : ((k : ℝ) / 2) ^ (-c) = 2 ^ c * (k : ℝ) ^ (-c) := by
    rw [Real.div_rpow (Nat.cast_nonneg k) (by norm_num) (-c)]
    rw [div_eq_mul_inv, Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2)]
    rw [inv_inv, mul_comm]
  linarith [h4, h5]

-- helper: (k+1)^p ≤ 2^p k^p for k ≥ 1, p ≥ 0
private theorem rpow_succ_le (k : ℕ) (hk : 1 ≤ k) (p : ℝ) (hp : 0 ≤ p) :
    ((k : ℝ) + 1) ^ p ≤ 2 ^ p * (k : ℝ) ^ p := by
  have hkR : (0 : ℝ) < (k : ℝ) := by
    have : 0 < k := by omega
    exact_mod_cast this
  have hle : (k : ℝ) + 1 ≤ 2 * (k : ℝ) := by
    have : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    linarith
  have h3 : ((k : ℝ) + 1) ^ p ≤ (2 * (k : ℝ)) ^ p :=
    Real.rpow_le_rpow (by linarith) hle hp
  rwa [Real.mul_rpow (by norm_num) hkR.le] at h3

-- k-form eventual bound for tterm (β ≥ 1)
private theorem tterm_event_bound (A C c : ℝ) (hA : A = C - c) (hC : 0 < C) (hc : 0 < c)
    (n β : ℕ) (_hβn : β ≤ n) (_hnc : (n : ℝ) < c) (hβ1 : 1 ≤ β) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ k : ℕ in atTop,
      ‖tterm A C (β : ℝ) k‖ ≤ K * (k : ℝ) ^ ((β : ℝ) - 1 - c) := by
  obtain ⟨M, hMpos, hevM⟩ := poch_ratio_rpow_bound A C c hA hC hc
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hevM
  have hKnn : (0 : ℝ) ≤ M * 2 ^ c * 2 ^ ((β : ℝ) - 1) :=
    mul_nonneg (mul_nonneg hMpos.le (Real.rpow_nonneg (by norm_num) _))
      (Real.rpow_nonneg (by norm_num) _)
  refine ⟨M * 2 ^ c * 2 ^ ((β : ℝ) - 1), hKnn, ?_⟩
  filter_upwards [eventually_ge_atTop (max 2 (N + 1))] with k hk
  have hk2 : 2 ≤ k := le_trans (le_max_left _ _) hk
  have hkN : N + 1 ≤ k := le_trans (le_max_right _ _) hk
  have hk1 : 1 ≤ k := by omega
  have hkR : (0 : ℝ) < (k : ℝ) := by
    have : 0 < k := by omega
    exact_mod_cast this
  have hsub : k - 1 + 1 = k := by omega
  have hcastsub : (((k - 1 : ℕ)) : ℝ) = (k : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ k), Nat.cast_one]
  have hkm1 : N ≤ k - 1 := by omega
  have hbound := hN (k - 1) hkm1
  rw [hsub] at hbound
  rw [hcastsub] at hbound
  have hAC : |(ascPochhammer ℝ k).eval A / (ascPochhammer ℝ k).eval C|
      ≤ M * 2 ^ c * (k : ℝ) ^ (-c) := by
    have h1 := rpow_neg_sub_le k hk2 c hc
    calc |(ascPochhammer ℝ k).eval A / (ascPochhammer ℝ k).eval C|
        ≤ M * ((k : ℝ) - 1) ^ (-c) := hbound
      _ ≤ M * (2 ^ c * (k : ℝ) ^ (-c)) := mul_le_mul_of_nonneg_left h1 hMpos.le
      _ = M * 2 ^ c * (k : ℝ) ^ (-c) := by ring
  have hB := poch_nat_le β k hβ1
  have hβexp : (0 : ℝ) ≤ (β : ℝ) - 1 := by
    have : (1 : ℝ) ≤ (β : ℝ) := by exact_mod_cast hβ1
    linarith
  have hB2 : ((k : ℝ) + 1) ^ ((β : ℝ) - 1) ≤ 2 ^ ((β : ℝ) - 1) * (k : ℝ) ^ ((β : ℝ) - 1) :=
    rpow_succ_le k hk1 _ hβexp
  have hBnn : (0 : ℝ) ≤ (ascPochhammer ℝ k).eval (β : ℝ) / (Nat.factorial k : ℝ) := by
    apply div_nonneg _ (Nat.cast_nonneg _)
    apply le_of_lt
    apply ascPochhammer_pos
    exact_mod_cast (by omega : 0 < β)
  have hACnn : (0 : ℝ) ≤ M * 2 ^ c * (k : ℝ) ^ (-c) :=
    mul_nonneg (mul_nonneg hMpos.le (Real.rpow_nonneg (by norm_num) _))
      (Real.rpow_nonneg hkR.le _)
  have hBB : (ascPochhammer ℝ k).eval (β : ℝ) / (Nat.factorial k : ℝ)
      ≤ 2 ^ ((β : ℝ) - 1) * (k : ℝ) ^ ((β : ℝ) - 1) := le_trans hB hB2
  have ht_eq : tterm A C (β : ℝ) k
      = ((ascPochhammer ℝ k).eval A / (ascPochhammer ℝ k).eval C)
        * ((ascPochhammer ℝ k).eval (β : ℝ) / (Nat.factorial k : ℝ)) := by
    rw [tterm]; ring
  rw [ht_eq, Real.norm_eq_abs, abs_mul, abs_of_nonneg hBnn]
  calc |(ascPochhammer ℝ k).eval A / (ascPochhammer ℝ k).eval C|
        * ((ascPochhammer ℝ k).eval (β : ℝ) / (Nat.factorial k : ℝ))
      ≤ (M * 2 ^ c * (k : ℝ) ^ (-c)) * (2 ^ ((β : ℝ) - 1) * (k : ℝ) ^ ((β : ℝ) - 1)) :=
        mul_le_mul hAC hBB hBnn hACnn
    _ = (M * 2 ^ c * 2 ^ ((β : ℝ) - 1)) * (k : ℝ) ^ ((β : ℝ) - 1 - c) := by
      have hrw : (k : ℝ) ^ (-c) * (k : ℝ) ^ ((β : ℝ) - 1) = (k : ℝ) ^ ((β : ℝ) - 1 - c) := by
        rw [← Real.rpow_add hkR]
        congr 1
        ring
      have hring : (M * 2 ^ c * (k : ℝ) ^ (-c)) * (2 ^ ((β : ℝ) - 1) * (k : ℝ) ^ ((β : ℝ) - 1))
          - (M * 2 ^ c * 2 ^ ((β : ℝ) - 1)) * ((k : ℝ) ^ (-c) * (k : ℝ) ^ ((β : ℝ) - 1)) = 0 := by
        ring
      linear_combination M * 2 ^ c * 2 ^ ((β : ℝ) - 1) * hrw + hring

-- summability of tterm
private theorem summable_tterm (A C c : ℝ) (hA : A = C - c) (hC : 0 < C) (hc : 0 < c)
    (n β : ℕ) (hβn : β ≤ n) (hnc : (n : ℝ) < c) :
    Summable (tterm A C (β : ℝ)) := by
  by_cases hβ0 : β = 0
  · subst hβ0
    have h0 : ∀ b' : ℕ, b' ≠ 0 → tterm A C (((0 : ℕ)) : ℝ) b' = 0 := by
      intro b' hb'
      have hcast : ((((0 : ℕ))) : ℝ) = (0 : ℝ) := by norm_cast
      rw [tterm, hcast]
      have hz : (ascPochhammer ℝ b').eval (0 : ℝ) = 0 := by
        rw [ascPochhammer_eval_zero]
        simp [hb']
      rw [hz, mul_zero, zero_div]
    have hH := hasSum_single (0 : ℕ) h0
    exact hH.summable
  · have hβ1 : 1 ≤ β := by omega
    obtain ⟨K, _, hevK⟩ := tterm_event_bound A C c hA hC hc n β hβn hnc hβ1
    have hexp : (β : ℝ) - 1 - c < -1 := by
      have hβnR : (β : ℝ) ≤ (n : ℝ) := by exact_mod_cast hβn
      linarith
    have hsum : Summable (fun k : ℕ => K * (k : ℝ) ^ ((β : ℝ) - 1 - c)) :=
      (Real.summable_nat_rpow.mpr hexp).mul_left K
    have hevC : ∀ᶠ k : ℕ in cofinite,
        ‖tterm A C (β : ℝ) k‖ ≤ K * (k : ℝ) ^ ((β : ℝ) - 1 - c) := by
      rwa [Nat.cofinite_eq_atTop]
    exact Summable.of_norm_bounded_eventually hsum hevC

-- k-form eventual bound for the Pochhammer ratio itself
private theorem AC_event_bound (A C c : ℝ) (hA : A = C - c) (hC : 0 < C) (hc : 0 < c) :
    ∃ KAC : ℝ, 0 ≤ KAC ∧ ∀ᶠ k : ℕ in atTop,
      |(ascPochhammer ℝ k).eval A / (ascPochhammer ℝ k).eval C|
        ≤ KAC * (k : ℝ) ^ (-c) := by
  obtain ⟨M, hMpos, hevM⟩ := poch_ratio_rpow_bound A C c hA hC hc
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hevM
  have hKnn : (0 : ℝ) ≤ M * 2 ^ c :=
    mul_nonneg hMpos.le (Real.rpow_nonneg (by norm_num) _)
  refine ⟨M * 2 ^ c, hKnn, ?_⟩
  filter_upwards [eventually_ge_atTop (max 2 (N + 1))] with k hk
  have hk2 : 2 ≤ k := le_trans (le_max_left _ _) hk
  have hkN : N + 1 ≤ k := le_trans (le_max_right _ _) hk
  have hsub : k - 1 + 1 = k := by omega
  have hcastsub : (((k - 1 : ℕ)) : ℝ) = (k : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ k), Nat.cast_one]
  have hkm1 : N ≤ k - 1 := by omega
  have hb := hN (k - 1) hkm1
  rw [hsub] at hb
  rw [hcastsub] at hb
  have h1 := rpow_neg_sub_le k hk2 c hc
  calc |(ascPochhammer ℝ k).eval A / (ascPochhammer ℝ k).eval C|
      ≤ M * ((k : ℝ) - 1) ^ (-c) := hb
    _ ≤ M * (2 ^ c * (k : ℝ) ^ (-c)) := mul_le_mul_of_nonneg_left h1 hMpos.le
    _ = (M * 2 ^ c) * (k : ℝ) ^ (-c) := by ring

private theorem vterm_succ (A C β : ℝ) (k : ℕ) : vterm A C β (k + 1) =
    (ascPochhammer ℝ (k + 1)).eval A * (ascPochhammer ℝ k).eval (β + 1) /
    ((ascPochhammer ℝ k).eval C * (Nat.factorial k : ℝ)) := rfl

-- vanishing of boundary terms
private theorem tendsto_vterm (A C c : ℝ) (hA : A = C - c) (hC : 0 < C) (hc : 0 < c)
    (n β : ℕ) (hβn : β + 1 ≤ n) (hnc : (n : ℝ) < c) :
    Tendsto (vterm A C (β : ℝ)) atTop (𝓝 0) := by
  obtain ⟨Kt, hKtnn, hevT⟩ := tterm_event_bound A C c hA hC hc n (β + 1) hβn hnc
    (Nat.succ_le_succ (Nat.zero_le β))
  have hexp2 : ((((β + 1 : ℕ))) : ℝ) - 1 - c = (β : ℝ) - c := by push_cast; ring
  rw [hexp2] at hevT
  have hexp : (β : ℝ) + 1 - c < 0 := by
    have hβnR : ((β : ℝ)) + 1 ≤ (n : ℝ) := by exact_mod_cast hβn
    linarith
  have hKnn : (0 : ℝ) ≤ Kt * (C + 1) :=
    mul_nonneg hKtnn (by linarith [hC])
  have hlim0 : Tendsto (fun k : ℕ => (Kt * (C + 1)) * (k : ℝ) ^ ((β : ℝ) + 1 - c))
      atTop (𝓝 0) := by
    have hpos : (0 : ℝ) < c - ((β : ℝ) + 1) := by linarith
    have h := (tendsto_rpow_neg_atTop hpos).comp tendsto_natCast_atTop_atTop
    have heq : ((β : ℝ) + 1 - c) = -(c - ((β : ℝ) + 1)) := by ring
    have hfun : (fun k : ℕ => (k : ℝ) ^ ((β : ℝ) + 1 - c))
        = ((fun x : ℝ => x ^ (-(c - ((β : ℝ) + 1)))) ∘ Nat.cast) := by
      funext k
      simp only [Function.comp_apply]
      rw [heq]
    have h2 : Tendsto (fun k : ℕ => (k : ℝ) ^ ((β : ℝ) + 1 - c)) atTop (𝓝 0) := by
      rw [hfun]
      exact h
    have h3 := h2.const_mul (Kt * (C + 1))
    rwa [mul_zero] at h3
  have hβc : ((β : ℕ) : ℝ) + 1 = ((((β + 1 : ℕ))) : ℝ) := by push_cast; ring
  have hbdd : ∀ᶠ k : ℕ in atTop,
      ‖vterm A C (β : ℝ) k‖ ≤ (Kt * (C + 1)) * (k : ℝ) ^ ((β : ℝ) + 1 - c) := by
    filter_upwards [eventually_ge_atTop 1, hevT] with k hk1 htk
    have hkR : (0 : ℝ) < (k : ℝ) := by
      have : 0 < k := by omega
      exact_mod_cast this
    have hkk : k - 1 + 1 = k := by omega
    have hcastsub : (((k - 1 : ℕ)) : ℝ) = (k : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ k), Nat.cast_one]
    have hβnn : (0 : ℝ) ≤ (β : ℝ) := Nat.cast_nonneg _
    have hβkpos : (0 : ℝ) < (β : ℝ) + (k : ℝ) := by linarith
    have hβk : (β : ℝ) + (k : ℝ) ≠ 0 := ne_of_gt hβkpos
    have hCkpos : (0 : ℝ) < C + (k : ℝ) - 1 := by linarith [hC, hkR]
    have hCk : C + (k : ℝ) - 1 ≠ 0 := ne_of_gt hCkpos
    have hCk1m : (ascPochhammer ℝ (k - 1)).eval C ≠ 0 :=
      ne_of_gt (ascPochhammer_pos _ _ hC)
    have hfactm : (Nat.factorial (k - 1) : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    have eB : (ascPochhammer ℝ k).eval ((β : ℝ) + 1)
        = (ascPochhammer ℝ (k - 1)).eval ((β : ℝ) + 1) * ((β : ℝ) + (k : ℝ)) := by
      have hfac : ((β : ℝ) + 1) + (((k - 1 : ℕ)) : ℝ) = (β : ℝ) + (k : ℝ) := by
        rw [hcastsub]; ring
      conv_lhs => rw [← hkk]
      rw [ascPochhammer_succ_eval, hfac]
    have eC : (ascPochhammer ℝ k).eval C
        = (ascPochhammer ℝ (k - 1)).eval C * (C + (k : ℝ) - 1) := by
      have hfac : C + (((k - 1 : ℕ)) : ℝ) = C + (k : ℝ) - 1 := by rw [hcastsub]; ring
      conv_lhs => rw [← hkk]
      rw [ascPochhammer_succ_eval, hfac]
    have eF : (Nat.factorial k : ℝ) = (k : ℝ) * (Nat.factorial (k - 1) : ℝ) := by
      conv_lhs => rw [← hkk]
      rw [Nat.factorial_succ]
      push_cast
      rw [hcastsub]
      ring
    have hv2 : vterm A C (β : ℝ) k
        = tterm A C ((β : ℝ) + 1) k
          * ((k : ℝ) * ((C + (k : ℝ) - 1) / ((β : ℝ) + (k : ℝ)))) := by
      conv_lhs => rw [← hkk]
      rw [vterm_succ, tterm, eB, eC, eF]
      field_simp
      rw [hkk]
      ring
    have hFnn : (0 : ℝ) ≤ (k : ℝ) * ((C + (k : ℝ) - 1) / ((β : ℝ) + (k : ℝ))) := by
      apply mul_nonneg hkR.le
      apply div_nonneg hCkpos.le hβkpos.le
    have hFle : (k : ℝ) * ((C + (k : ℝ) - 1) / ((β : ℝ) + (k : ℝ))) ≤ (C + 1) * (k : ℝ) := by
      have h1 : (C + (k : ℝ) - 1) / ((β : ℝ) + (k : ℝ)) ≤ C + 1 := by
        rw [div_le_iff₀ hβkpos]
        have e1 : (0 : ℝ) ≤ (C + 1) * (β : ℝ) :=
          mul_nonneg (by linarith [hC]) hβnn
        have e2 : (0 : ℝ) ≤ C * ((k : ℝ) - 1) :=
          mul_nonneg hC.le (by linarith [hkR, show (1:ℝ) ≤ (k:ℝ) from by exact_mod_cast hk1])
        nlinarith [e1, e2]
      calc (k : ℝ) * ((C + (k : ℝ) - 1) / ((β : ℝ) + (k : ℝ)))
          ≤ (k : ℝ) * (C + 1) := mul_le_mul_of_nonneg_left h1 hkR.le
        _ = (C + 1) * (k : ℝ) := by ring
    have htk2 : |tterm A C ((β : ℝ) + 1) k|
        ≤ Kt * (k : ℝ) ^ ((β : ℝ) - c) := by
      have htkA : ‖tterm A C (((β + 1 : ℕ)) : ℝ) k‖ ≤ Kt * (k : ℝ) ^ ((β : ℝ) - c) := htk
      rw [Real.norm_eq_abs] at htkA
      rwa [← hβc] at htkA
    have hKtnn2 : (0 : ℝ) ≤ Kt * (k : ℝ) ^ ((β : ℝ) - c) :=
      mul_nonneg hKtnn (Real.rpow_nonneg hkR.le _)
    rw [hv2, Real.norm_eq_abs, abs_mul, abs_of_nonneg hFnn]
    calc |tterm A C ((β : ℝ) + 1) k|
          * ((k : ℝ) * ((C + (k : ℝ) - 1) / ((β : ℝ) + (k : ℝ))))
        ≤ (Kt * (k : ℝ) ^ ((β : ℝ) - c)) * ((C + 1) * (k : ℝ)) :=
          mul_le_mul htk2 hFle hFnn hKtnn2
      _ = (Kt * (C + 1)) * (k : ℝ) ^ ((β : ℝ) + 1 - c) := by
        have hrw : (k : ℝ) ^ ((β : ℝ) - c) * (k : ℝ) = (k : ℝ) ^ ((β : ℝ) + 1 - c) := by
          have h := (Real.rpow_add hkR ((β : ℝ) - c) 1).symm
          rw [Real.rpow_one] at h
          rw [h]
          congr 1
          ring
        have hring : (Kt * (k : ℝ) ^ ((β : ℝ) - c)) * ((C + 1) * (k : ℝ))
            - (Kt * (C + 1)) * ((k : ℝ) ^ ((β : ℝ) - c) * (k : ℝ)) = 0 := by
          ring
        linear_combination (Kt * (C + 1)) * hrw + hring
  exact squeeze_zero_norm' hbdd hlim0

private theorem gamma_chain_pos (c : ℝ) (n : ℕ) (h : ∀ j : ℕ, j < n → 0 < c - ((j : ℝ) + 1)) :
    Real.Gamma c = Real.Gamma (c - (n : ℝ)) * ∏ j ∈ Finset.range n, (c - ((j : ℝ) + 1)) := by
  induction n generalizing c with
  | zero => simp
  | succ n ih =>
    have hc1 : (0 : ℝ) < c - 1 := by
      have h0 := h 0 (Nat.zero_lt_succ n)
      push_cast at h0 ⊢
      simpa using h0
    have hne : c - 1 ≠ 0 := ne_of_gt hc1
    have hrest : ∀ j : ℕ, j < n → 0 < (c - 1) - ((j : ℝ) + 1) := by
      intro j hj
      have hj2 : j + 1 < n + 1 := by omega
      have hh := h (j + 1) hj2
      push_cast at hh ⊢
      linarith
    have ih' := ih (c - 1) hrest
    have hG : Real.Gamma c = (c - 1) * Real.Gamma (c - 1) := by
      have harg : (c - 1) + 1 = c := by ring
      conv_lhs => rw [← harg]
      exact Real.Gamma_add_one hne
    have heq : (c - 1) - (n : ℝ) = c - (((n + 1 : ℕ)) : ℝ) := by push_cast; ring
    have hkey : ∏ j ∈ Finset.range (n + 1), (c - ((j : ℝ) + 1))
        = (c - 1) * ∏ j ∈ Finset.range n, ((c - 1) - ((j : ℝ) + 1)) := by
      rw [Finset.prod_range_succ', mul_comm]
      congr 1
      · push_cast; ring
      · apply Finset.prod_congr rfl
        intro j _
        push_cast; ring
    rw [hG, ih', heq, hkey]
    ring

-- Gamma chain with nonzero (no positivity needed)
private theorem gamma_chain_ne (s : ℝ) (n : ℕ) (h : ∀ j : ℕ, j < n → s - ((j : ℝ) + 1) ≠ 0) :
    Real.Gamma s = Real.Gamma (s - (n : ℝ)) * ∏ j ∈ Finset.range n, (s - ((j : ℝ) + 1)) := by
  induction n generalizing s with
  | zero => simp
  | succ n ih =>
    have hne : s - 1 ≠ 0 := by
      have h0 := h 0 (Nat.zero_lt_succ n)
      push_cast at h0 ⊢
      simpa using h0
    have hrest : ∀ j : ℕ, j < n → (s - 1) - ((j : ℝ) + 1) ≠ 0 := by
      intro j hj
      have hj2 : j + 1 < n + 1 := by omega
      have hh := h (j + 1) hj2
      push_cast at hh ⊢
      intro hcon
      apply hh
      linarith
    have ih' := ih (s - 1) hrest
    have hG : Real.Gamma s = (s - 1) * Real.Gamma (s - 1) := by
      have harg : (s - 1) + 1 = s := by ring
      conv_lhs => rw [← harg]
      exact Real.Gamma_add_one hne
    have heq : (s - 1) - (n : ℝ) = s - (((n + 1 : ℕ)) : ℝ) := by push_cast; ring
    have hkey : ∏ j ∈ Finset.range (n + 1), (s - ((j : ℝ) + 1))
        = (s - 1) * ∏ j ∈ Finset.range n, ((s - 1) - ((j : ℝ) + 1)) := by
      rw [Finset.prod_range_succ', mul_comm]
      congr 1
      · push_cast; ring
      · apply Finset.prod_congr rfl
        intro j _
        push_cast; ring
    rw [hG, ih', heq, hkey]
    ring

-- Step 1: RHS equals the finite product
private theorem rhs_eq_prod (n : ℕ) (b c : ℝ) (hcn : (n : ℝ) < c) (hb : -1 < b) :
    Real.Gamma (c - (n : ℝ)) * Real.Gamma (b + 1) /
      (Real.Gamma c * Real.Gamma (b - (n : ℝ) + 1))
      = ∏ j ∈ Finset.range n, ((b - (j : ℝ)) / (c - ((j : ℝ) + 1))) := by
  have hcpos : ∀ j : ℕ, j < n → 0 < c - ((j : ℝ) + 1) := by
    intro j hj
    have hjn : ((j : ℝ) + 1) ≤ (n : ℝ) := by
      have : j + 1 ≤ n := by omega
      have h1 : ((j + 1 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast this
      push_cast at h1
      linarith
    linarith
  have hGc := gamma_chain_pos c n hcpos
  have hPc_pos : 0 < ∏ j ∈ Finset.range n, (c - ((j : ℝ) + 1)) := by
    apply Finset.prod_pos
    intro j hj
    exact hcpos j (Finset.mem_range.mp hj)
  have hPc_ne : (∏ j ∈ Finset.range n, (c - ((j : ℝ) + 1))) ≠ 0 := ne_of_gt hPc_pos
  have hGc_ne : Real.Gamma c ≠ 0 := by
    have hc0 : 0 < c := by
      have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    exact ne_of_gt (Real.Gamma_pos_of_pos hc0)
  have hGcn_ne : Real.Gamma (c - (n : ℝ)) ≠ 0 := by
    have : 0 < c - (n : ℝ) := by linarith
    exact ne_of_gt (Real.Gamma_pos_of_pos this)
  by_cases hdeg : ∃ m : ℕ, b + 1 - (n : ℝ) = -((m : ℕ) : ℝ)
  · -- degenerate case: both sides zero
    obtain ⟨m, hm⟩ := hdeg
    have hGb0 : Real.Gamma (b - (n : ℝ) + 1) = 0 := by
      have heq : b - (n : ℝ) + 1 = -((m : ℕ) : ℝ) := by linarith
      rw [heq]
      exact Real.Gamma_neg_nat_eq_zero m
    have hRHS0 : Real.Gamma (c - (n : ℝ)) * Real.Gamma (b + 1) /
        (Real.Gamma c * Real.Gamma (b - (n : ℝ) + 1)) = 0 := by
      rw [hGb0, mul_zero, div_zero]
    rw [hRHS0]
    -- the product has a zero factor at j = n-1-m
    have hmn : m < n := by
      by_contra hcon
      have hcon2 : n ≤ m := by omega
      have hmR : ((m : ℕ) : ℝ) ≥ (n : ℝ) := by exact_mod_cast hcon2
      linarith
    have hbnat : b = ((n - 1 - m : ℕ) : ℝ) := by
      have hbeq : b = (n : ℝ) - 1 - (m : ℝ) := by linarith
      have hcast : ((n - 1 - m : ℕ) : ℝ) = (n : ℝ) - 1 - (m : ℝ) := by
        have h1 : m + 1 ≤ n := by omega
        have h2 : n - 1 - m + (m + 1) = n := by omega
        have h3 : ((n - 1 - m : ℕ) : ℝ) + (((m + 1 : ℕ)) : ℝ) = (n : ℝ) := by
          have := congrArg (Nat.cast : ℕ → ℝ) h2
          push_cast at this ⊢
          linarith [this]
        push_cast at h3 ⊢
        linarith
      rw [hcast] at *
      linarith
    have hj0mem : n - 1 - m ∈ Finset.range n := by
      rw [Finset.mem_range]
      omega
    symm
    apply Finset.prod_eq_zero hj0mem
    rw [hbnat]
    simp
  · -- non-degenerate case
    rw [not_exists] at hdeg
    have hbne : ∀ j : ℕ, j < n → (b + 1) - ((j : ℝ) + 1) ≠ 0 := by
      intro j hj hcon
      have hbj : b = (j : ℝ) := by linarith
      have hmn : n - 1 - j < n := by omega
      -- m := n-1-j, then b+1-n = -m
      set m := n - 1 - j with hmdef
      have hcast : ((m : ℕ) : ℝ) = (n : ℝ) - 1 - (j : ℝ) := by
        have h2 : m + (j + 1) = n := by omega
        have h3 : ((m : ℕ) : ℝ) + (((j + 1 : ℕ)) : ℝ) = (n : ℝ) := by exact_mod_cast h2
        push_cast at h3 ⊢
        linarith
      apply hdeg m
      rw [hbj, hcast]
      ring
    have hGb := gamma_chain_ne (b + 1) n hbne
    have hGbn_ne : Real.Gamma (b - (n : ℝ) + 1) ≠ 0 := by
      have heq : b - (n : ℝ) + 1 = b + 1 - (n : ℝ) := by ring
      rw [heq]
      apply Real.Gamma_ne_zero
      intro m
      exact hdeg m
    have hGb1_ne : Real.Gamma (b + 1) ≠ 0 := by
      rw [hGb]
      apply mul_ne_zero
      · have heq : b + 1 - (n : ℝ) = b - (n : ℝ) + 1 := by ring
        rw [heq]
        exact hGbn_ne
      · apply Finset.prod_ne_zero_iff.mpr
        intro j hj
        exact hbne j (Finset.mem_range.mp hj)
    have heq2 : b + 1 - (n : ℝ) = b - (n : ℝ) + 1 := by ring
    have hprod : ∏ j ∈ Finset.range n, (b + 1 - ((j : ℝ) + 1))
        = ∏ j ∈ Finset.range n, (b - (j : ℝ)) := by
      apply Finset.prod_congr rfl
      intro j _
      ring
    rw [hGb, heq2, hprod, hGc, Finset.prod_div_distrib]
    field_simp

private theorem poch_left_eval (s : ℝ) (m : ℕ) :
    (ascPochhammer ℝ (m + 1)).eval s = s * (ascPochhammer ℝ m).eval (s + 1) := by
  have h := ascPochhammer_succ_left ℝ m
  have h2 := congrArg (fun p => Polynomial.eval s p) h
  simp only [Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_comp,
    Polynomial.eval_add, Polynomial.eval_one] at h2
  exact h2

private theorem vterm_zero (A C β : ℝ) : vterm A C β 0 = 0 := rfl

private theorem tterm_zero (A C β : ℝ) : tterm A C β 0 = 1 := by
  simp [tterm]

-- contiguous relation

private theorem contiguous (A C β c : ℝ) (hA : A = C - c)
    (hC : ∀ k : ℕ, (ascPochhammer ℝ k).eval C ≠ 0) (k : ℕ) :
    (c - β - 1) * tterm A C (β + 1) k - (C - β - 1) * tterm A C β k
      = vterm A C β k - vterm A C β (k + 1) := by
  cases k with
  | zero =>
    rw [tterm_zero, tterm_zero, vterm_zero, vterm_succ]
    simp only [ascPochhammer_zero, Polynomial.eval_one, Nat.factorial_zero, Nat.cast_one,
      mul_one]
    rw [ascPochhammer_one]
    simp only [Polynomial.eval_X]
    rw [hA]
    ring
  | succ m =>
    have hCm : (ascPochhammer ℝ m).eval C ≠ 0 := hC m
    have hCm1 : (ascPochhammer ℝ (m + 1)).eval C ≠ 0 := hC (m + 1)
    have hfactm : (Nat.factorial m : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero m)
    have hfactm1 : (Nat.factorial (m + 1) : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (m + 1))
    -- Pochhammer recursions
    have e1 : (ascPochhammer ℝ (m + 1)).eval β
        = β * (ascPochhammer ℝ m).eval (β + 1) := poch_left_eval β m
    have e2 : (ascPochhammer ℝ (m + 1)).eval (β + 1)
        = (ascPochhammer ℝ m).eval (β + 1) * (β + 1 + (m : ℝ)) :=
      ascPochhammer_succ_eval m (β + 1)
    have e3 : (ascPochhammer ℝ (m + 1 + 1)).eval A
        = (ascPochhammer ℝ (m + 1)).eval A * (A + ((m + 1 : ℕ) : ℝ)) :=
      ascPochhammer_succ_eval (m + 1) A
    have e4 : (ascPochhammer ℝ (m + 1)).eval C
        = (ascPochhammer ℝ m).eval C * (C + (m : ℝ)) :=
      ascPochhammer_succ_eval m C
    have efact : (Nat.factorial (m + 1) : ℝ)
        = ((m + 1 : ℕ) : ℝ) * (Nat.factorial m : ℝ) := by
      rw [Nat.factorial_succ]
      push_cast
      ring
    have hcast1 : ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by push_cast; ring
    have hCpm : C + (m : ℝ) ≠ 0 := by
      intro hcon
      apply hCm1
      rw [e4, hcon, mul_zero]
    have hm1 : ((m + 1 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero m
    change (c - β - 1) * tterm A C (β + 1) (m + 1) - (C - β - 1) * tterm A C β (m + 1)
      = vterm A C β (m + 1) - vterm A C β (m + 1 + 1)
    rw [tterm, tterm, vterm_succ, vterm_succ]
    rw [e1, e2, e3, e4, efact]
    field_simp
    rw [hA, hcast1]
    ring

-- Step 5: finite product and induction on beta
private noncomputable def Pprod (C c : ℝ) (β : ℕ) : ℝ :=
  ∏ j ∈ Finset.range β, ((C - ((j : ℝ) + 1)) / (c - ((j : ℝ) + 1)))

private theorem hasSum_tterm_zero (A C : ℝ) :
    HasSum (tterm A C 0) 1 := by
  have h0 : ∀ b' : ℕ, b' ≠ 0 → tterm A C 0 b' = 0 := by
    intro b' hb'
    rw [tterm]
    have hz : (ascPochhammer ℝ b').eval (0 : ℝ) = 0 := by
      rw [ascPochhammer_eval_zero]
      simp [hb']
    rw [hz, mul_zero, zero_div]
  have hH := hasSum_single (0 : ℕ) h0
  rwa [tterm_zero] at hH

private theorem base_case (A C c : ℝ) : HasSum (tterm A C (((0 : ℕ)) : ℝ)) (Pprod C c 0) := by
  rw [Nat.cast_zero]
  have hP : Pprod C c 0 = 1 := by simp [Pprod]
  rw [hP]
  exact hasSum_tterm_zero A C

private theorem step_case (A C c : ℝ) (hA : A = C - c) (hC : 0 < C) (hc : 0 < c)
    (n β : ℕ) (hnc : (n : ℝ) < c) (hβn : β + 1 ≤ n)
    (hIH : HasSum (tterm A C (β : ℝ)) (Pprod C c β)) :
    HasSum (tterm A C ((((β + 1 : ℕ))) : ℝ)) (Pprod C c (β + 1)) := by
  have hCne : ∀ k : ℕ, (ascPochhammer ℝ k).eval C ≠ 0 :=
    fun k => ne_of_gt (ascPochhammer_pos k C hC)
  have hs1 : Summable (tterm A C (β : ℝ)) :=
    summable_tterm A C c hA hC hc n β (by omega) hnc
  have hs2 : Summable (tterm A C ((((β + 1 : ℕ))) : ℝ)) :=
    summable_tterm A C c hA hC hc n (β + 1) hβn hnc
  have hβc : ((((β + 1 : ℕ))) : ℝ) = (β : ℝ) + 1 := by push_cast; ring
  have haPos : (0 : ℝ) < c - (β : ℝ) - 1 := by
    have hβnR : ((β : ℝ)) + 1 ≤ (n : ℝ) := by exact_mod_cast hβn
    linarith
  have haNe : (c - (β : ℝ) - 1) ≠ 0 := ne_of_gt haPos
  have hgsum : Summable (fun k : ℕ => (c - (β : ℝ) - 1) * tterm A C ((((β + 1 : ℕ))) : ℝ) k
      - (C - (β : ℝ) - 1) * tterm A C (β : ℝ) k) :=
    (hs2.mul_left _).sub (hs1.mul_left _)
  have htele : ∀ K : ℕ, (∑ i ∈ Finset.range K, ((c - (β : ℝ) - 1)
      * tterm A C ((((β + 1 : ℕ))) : ℝ) i - (C - (β : ℝ) - 1) * tterm A C (β : ℝ) i))
      = -(vterm A C (β : ℝ) K) := by
    intro K
    have h1 : (∑ i ∈ Finset.range K, ((c - (β : ℝ) - 1)
        * tterm A C ((((β + 1 : ℕ))) : ℝ) i - (C - (β : ℝ) - 1) * tterm A C (β : ℝ) i))
        = ∑ i ∈ Finset.range K, (vterm A C (β : ℝ) i - vterm A C (β : ℝ) (i + 1)) := by
      apply Finset.sum_congr rfl
      intro i _
      have hc := contiguous A C (β : ℝ) c hA hCne i
      rw [hβc]
      exact hc
    rw [h1, Finset.sum_range_sub', vterm_zero, zero_sub]
  have hlimR : Tendsto (fun K : ℕ => -(vterm A C (β : ℝ) K)) atTop (𝓝 0) := by
    have h := (tendsto_vterm A C c hA hC hc n β hβn hnc).neg
    rwa [neg_zero] at h
  have hSeq : (fun K : ℕ => ∑ i ∈ Finset.range K, ((c - (β : ℝ) - 1)
      * tterm A C ((((β + 1 : ℕ))) : ℝ) i - (C - (β : ℝ) - 1) * tterm A C (β : ℝ) i))
      = (fun K : ℕ => -(vterm A C (β : ℝ) K)) := funext htele
  have htsum0 : (∑' k : ℕ, ((c - (β : ℝ) - 1) * tterm A C ((((β + 1 : ℕ))) : ℝ) k
      - (C - (β : ℝ) - 1) * tterm A C (β : ℝ) k)) = 0 := by
    have hL := hgsum.hasSum.tendsto_sum_nat
    rw [hSeq] at hL
    exact tendsto_nhds_unique hL hlimR
  have hH2 : HasSum (fun k : ℕ => (c - (β : ℝ) - 1) * tterm A C ((((β + 1 : ℕ))) : ℝ) k
      - (C - (β : ℝ) - 1) * tterm A C (β : ℝ) k)
      ((c - (β : ℝ) - 1) * (∑' k : ℕ, tterm A C ((((β + 1 : ℕ))) : ℝ) k)
        - (C - (β : ℝ) - 1) * (Pprod C c β)) :=
    (hs2.hasSum.mul_left _).sub (hIH.mul_left _)
  have htsum_eq := hH2.tsum_eq
  rw [htsum0] at htsum_eq
  have hS : (∑' k : ℕ, tterm A C ((((β + 1 : ℕ))) : ℝ) k)
      = ((C - (β : ℝ) - 1) / (c - (β : ℝ) - 1)) * (Pprod C c β) := by
    have h1 : (c - (β : ℝ) - 1) * (∑' k : ℕ, tterm A C ((((β + 1 : ℕ))) : ℝ) k)
        = (C - (β : ℝ) - 1) * (Pprod C c β) := by linarith
    rw [div_mul_eq_mul_div, eq_div_iff haNe]
    linarith
  have hP : Pprod C c (β + 1)
      = ((C - (β : ℝ) - 1) / (c - (β : ℝ) - 1)) * (Pprod C c β) := by
    simp only [Pprod]
    rw [Finset.prod_range_succ]
    have e1 : C - (((β : ℕ) : ℝ) + 1) = C - (β : ℝ) - 1 := by ring
    have e2 : c - (((β : ℕ) : ℝ) + 1) = c - (β : ℝ) - 1 := by ring
    rw [e1, e2]
    exact mul_comm _ _
  have hfinal : (∑' k : ℕ, tterm A C ((((β + 1 : ℕ))) : ℝ) k) = Pprod C c (β + 1) := by
    rw [hS, hP]
  have hcon := hs2.hasSum
  rwa [hfinal] at hcon

private theorem hasSum_tterm_prod (A C c : ℝ) (hA : A = C - c) (hC : 0 < C) (hc : 0 < c)
    (n : ℕ) (hnc : (n : ℝ) < c) (m : ℕ) (hmn : m ≤ n) :
    HasSum (tterm A C (m : ℝ)) (Pprod C c m) := by
  have key : ∀ m : ℕ, m ≤ n → HasSum (tterm A C (m : ℝ)) (Pprod C c m) := by
    intro m
    induction m with
    | zero =>
      intro _
      exact base_case A C c
    | succ m ih =>
      intro hm
      exact step_case A C c hA hC hc n m hnc hm (ih (by omega))
  exact key m hmn

set_option linter.unusedVariables false in
/-- **Gauss summation at Frisch's specialization.** Let $n \ge 1$ be an integer and let $b$ and
$c$ be real numbers with $c > n$ and $b > -1$. Then
$$
{}_2F_1(1 + b - c, n; b + 1; 1) =
  \frac{\Gamma(c - n)\,\Gamma(b + 1)}{\Gamma(c)\,\Gamma(b - n + 1)},
$$
where ${}_2F_1(\alpha, \beta; \gamma; 1) =
\sum_{k \ge 0} \frac{(\alpha)_k (\beta)_k}{(\gamma)_k\, k!}$ and $(x)_k$ is the rising factorial.

The Gamma function is taken to be $0$ at its poles and division by $0$ gives $0$, so the right
side is $0$ when $b - n + 1$ is a nonpositive integer.

Source: Ulrich Abel, "A Short Proof of the Binomial Identities of Frisch and
Klamkin," Journal of Integer Sequences 23 (2020), Article 20.7.1, displayed
Frisch specialization at source lines 200-205 of the official TeX
`https://cs.uwaterloo.ca/journals/JIS/VOL23/Abel/abel12.tex`.

Proves `Wanted` entry `gauss_hypergeometric_summation_frisch`.
-/
theorem gauss_hypergeometric_summation_frisch (n : ℕ) (hn : 1 ≤ n) (b c : ℝ)
    (hcn : (n : ℝ) < c) (hb : -1 < b) :
    ordinaryHypergeometric (1 + b - c) (n : ℝ) (b + 1) (1 : ℝ) =
      Real.Gamma (c - n) * Real.Gamma (b + 1) /
        (Real.Gamma c * Real.Gamma (b - n + 1)) := by
  have hCpos : (0 : ℝ) < b + 1 := by linarith
  have hcpos : (0 : ℝ) < c := by
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hAeq : (1 : ℝ) + b - c = (b + 1) - c := by ring
  have hLHS : ordinaryHypergeometric (1 + b - c) (n : ℝ) (b + 1) (1 : ℝ)
      = ∑' k : ℕ, tterm (1 + b - c) (b + 1) (n : ℝ) k := by
    have h := ordinaryHypergeometric_sum_eq (1 + b - c) ((n : ℝ)) (b + 1) (1 : ℝ)
    unfold ordinaryHypergeometric
    rw [h]
    apply tsum_congr
    intro k
    have hCk : (ascPochhammer ℝ k).eval (b + 1) ≠ 0 :=
      ne_of_gt (ascPochhammer_pos _ _ hCpos)
    have hfk : (Nat.factorial k : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
    rw [tterm]
    simp only [one_pow, smul_eq_mul, mul_one]
    field_simp
  have hP := (hasSum_tterm_prod (1 + b - c) (b + 1) c hAeq hCpos hcpos n hcn n le_rfl).tsum_eq
  have hRHS : Real.Gamma (c - (n : ℝ)) * Real.Gamma (b + 1)
      / (Real.Gamma c * Real.Gamma (b - (n : ℝ) + 1)) = Pprod (b + 1) c n := by
    have h := rhs_eq_prod n b c hcn hb
    rw [h]
    simp only [Pprod]
    apply Finset.prod_congr rfl
    intro j _
    have e1 : (b : ℝ) + 1 - ((j : ℝ) + 1) = b - (j : ℝ) := by ring
    rw [e1]
  rw [hLHS, hP, hRHS]

end
end MetaMathlibExt
