/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Code.Onsager.KWMatrix
import Code.Onsager.ShermanLoop
import Code.Onsager.TurningTelescope
import Code.Onsager.TurnReversal






























namespace StatMech.Onsager

open Matrix BigOperators










theorem ons_loopWeight_KW_eq {L n : ℕ} [NeZero L] [NeZero n] (x ω : ℂ)
    (v : Fin n → ons_Dart L)
    (hvalid : ∀ k : Fin n, (v k).1 = ons_dirStep L (v (k + 1)).2 (v (k + 1)).1) :
    ons_loopWeight (ons_KWmat L x ω) v
      = x ^ n * ∏ k : Fin n, ons_turnW ω (v (k + 1)).2 (v k).2 := by
  unfold ons_loopWeight
  have hfac : ∀ k : Fin n, ons_KWmat L x ω (v k) (v (k + 1))
      = x * ons_turnW ω (v (k + 1)).2 (v k).2 := by
    intro k
    simp only [ons_KWmat]
    rw [if_pos (hvalid k)]
  calc ∏ k : Fin n, ons_KWmat L x ω (v k) (v (k + 1))
      = ∏ k : Fin n, (x * ons_turnW ω (v (k + 1)).2 (v k).2) :=
        Finset.prod_congr rfl (fun k _ => hfac k)
    _ = (∏ _k : Fin n, x) * ∏ k : Fin n, ons_turnW ω (v (k + 1)).2 (v k).2 :=
        Finset.prod_mul_distrib
    _ = x ^ n * ∏ k : Fin n, ons_turnW ω (v (k + 1)).2 (v k).2 := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]






theorem ons_rev_nonUturn (n : ℕ) (d : Fin (n + 1) → Fin 4)
    (hnu : ∀ k : Fin n, d k.succ ≠ d k.castSucc + 2) :
    ∀ k : Fin n, (fun j => d (Fin.rev j) + 2) k.succ
      ≠ (fun j => d (Fin.rev j) + 2) k.castSucc + 2 := by
  intro k
  have e1 : Fin.rev k.succ = (Fin.rev k).castSucc := by
    apply Fin.ext; simp only [Fin.val_rev, Fin.val_succ, Fin.val_castSucc]; omega
  have e2 : Fin.rev k.castSucc = (Fin.rev k).succ := by
    apply Fin.ext; simp only [Fin.val_rev, Fin.val_succ, Fin.val_castSucc]; omega
  simp only []
  rw [e1, e2]
  intro hc
  
  rw [add_assoc, show (2 : Fin 4) + 2 = 0 from by decide, add_zero] at hc
  
  exact hnu (Fin.rev k) hc.symm






theorem ons_walk_prod_rev (ω : ℂ) (hω : ω ≠ 0) (n : ℕ) (d : Fin (n + 1) → Fin 4)
    (hnu : ∀ k : Fin n, d k.succ ≠ d k.castSucc + 2) :
    ∏ k : Fin n, ons_turnW ω ((fun j => d (Fin.rev j) + 2) k.castSucc)
        ((fun j => d (Fin.rev j) + 2) k.succ)
      = (∏ k : Fin n, ons_turnW ω (d k.castSucc) (d k.succ))⁻¹ := by
  rw [ons_walk_prod_eq ω hω n (fun j => d (Fin.rev j) + 2) (ons_rev_nonUturn n d hnu),
    ons_walk_prod_eq ω hω n d hnu, ons_turnPow_sum_rev n d, _root_.zpow_neg]












theorem ons_walk_prod_rev_antipodal (ω : ℂ) (hω : ω ≠ 0) (hI : ω ^ 2 = Complex.I)
    (n : ℕ) (d : Fin (n + 1) → Fin 4)
    (hnu : ∀ k : Fin n, d k.succ ≠ d k.castSucc + 2)
    (hend : d (Fin.last n) = d 0 + 2) :
    ∏ k : Fin n, ons_turnW ω ((fun j => d (Fin.rev j) + 2) k.castSucc)
        ((fun j => d (Fin.rev j) + 2) k.succ)
      = - ∏ k : Fin n, ons_turnW ω (d k.castSucc) (d k.succ) := by
  
  have key : ∀ z : ℂ, z ^ 2 = -1 → z⁻¹ = -z := by
    intro z hz
    have h1 : z * (-z) = 1 := by rw [mul_neg, ← pow_two, hz]; ring
    exact inv_eq_of_mul_eq_one_right h1
  
  set S := ∑ k : Fin n, ons_turnPow (d k.castSucc) (d k.succ) with hS
  
  have hmod : ((S : ℤ) : ZMod 4) = 2 := by
    rw [hS, ons_walk_turnPow_mod n d hnu, hend]
    generalize d 0 = a
    fin_cases a <;> rfl
  obtain ⟨m, hm⟩ : ∃ m : ℤ, S = 4 * m + 2 := by
    have hzero : (((S : ℤ) - 2 : ℤ) : ZMod 4) = 0 := by
      rw [Int.cast_sub, hmod]; decide
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hzero
    obtain ⟨k, hk⟩ := hzero
    exact ⟨k, by push_cast at hk; linarith⟩
  
  have hval : ∏ k : Fin n, ons_turnW ω (d k.castSucc) (d k.succ) = ω ^ S :=
    ons_walk_prod_eq ω hω n d hnu
  
  have h4 : ω ^ (4 : ℤ) = -1 := by
    rw [show (4 : ℤ) = ((4 : ℕ) : ℤ) from rfl, zpow_natCast]
    exact ons_omega_pow_four ω hI
  
  have hPsq : (ω ^ S) ^ 2 = -1 := by
    rw [hm, pow_two, ← zpow_add₀ hω, show (4 * m + 2) + (4 * m + 2) = 4 * (2 * m + 1) from by ring,
      _root_.zpow_mul, h4]
    have hodd : (-1 : ℂ) ^ (2 * m + 1 : ℤ) = -1 := by
      rw [zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0), _root_.zpow_mul]
      norm_num
    exact hodd
  rw [ons_walk_prod_rev ω hω n d hnu, hval, key (ω ^ S) hPsq]














































end StatMech.Onsager
