/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Code.Onsager.KWMatrix
import Code.Onsager.TurningTelescope





















































namespace StatMech.Onsager

open BigOperators




theorem ons_neg_one_zpow_odd {m : ℤ} (h : Odd m) : (-1 : ℂ) ^ m = -1 := by
  obtain ⟨k, rfl⟩ := h
  rw [zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0), zpow_mul,
    show ((-1 : ℂ) ^ (2 : ℤ)) = 1 from by norm_num, one_zpow, one_mul, zpow_one]








theorem ons_closed_walk_prod (ω : ℂ) (hω : ω ≠ 0) (hI : ω ^ 2 = Complex.I)
    (n : ℕ) (d : Fin (n + 1) → Fin 4)
    (hnu : ∀ k : Fin n, d k.succ ≠ d k.castSucc + 2)
    (hclose : d (Fin.last n) = d 0) :
    ∃ m : ℤ,
      (∑ k : Fin n, ons_turnPow (d k.castSucc) (d k.succ)) = 4 * m ∧
      ∏ k : Fin n, ons_turnW ω (d k.castSucc) (d k.succ) = (-1) ^ m := by
  
  have hmod : ((∑ k : Fin n, ons_turnPow (d k.castSucc) (d k.succ) : ℤ) : ZMod 4) = 0 := by
    rw [ons_walk_turnPow_mod n d hnu, hclose]; exact sub_self _
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hmod
  obtain ⟨m, hm⟩ := hmod
  refine ⟨m, hm, ?_⟩
  have h4 : ω ^ ((4 : ℕ) : ℤ) = -1 := by
    rw [zpow_natCast]; exact ons_omega_pow_four ω hI
  rw [ons_walk_prod_eq ω hω n d hnu, hm, zpow_mul, h4]







theorem ons_selfAvoiding_prod (ω : ℂ) (hω : ω ≠ 0) (hI : ω ^ 2 = Complex.I)
    (n : ℕ) (d : Fin (n + 1) → Fin 4)
    (hnu : ∀ k : Fin n, d k.succ ≠ d k.castSucc + 2)
    (m : ℤ) (hm : (∑ k : Fin n, ons_turnPow (d k.castSucc) (d k.succ)) = 4 * m)
    (hwind : Odd m) :
    ∏ k : Fin n, ons_turnW ω (d k.castSucc) (d k.succ) = -1 := by
  have h4 : ω ^ (4 : ℤ) = -1 := by
    rw [show (4 : ℤ) = ((4 : ℕ) : ℤ) from rfl, zpow_natCast]
    exact ons_omega_pow_four ω hI
  rw [ons_walk_prod_eq ω hω n d hnu, hm, zpow_mul, h4]
  exact ons_neg_one_zpow_odd hwind







theorem ons_unitSquare_prod (ω : ℂ) (hω : ω ≠ 0) (hI : ω ^ 2 = Complex.I) :
    ∏ k : Fin 4, ons_turnW ω ((![0, 1, 2, 3, 0] : Fin 5 → Fin 4) k.castSucc)
        ((![0, 1, 2, 3, 0] : Fin 5 → Fin 4) k.succ) = -1 := by
  refine ons_selfAvoiding_prod ω hω hI 4 (![0, 1, 2, 3, 0] : Fin 5 → Fin 4) ?_ 1 ?_ odd_one
  · decide
  · decide





def ons_SelfAvoiding {L n : ℕ} (site : Fin (n + 1) → ZMod L × ZMod L) : Prop :=
  Function.Injective (fun k : Fin n => site k.castSucc)










def ons_DiscreteUmlaufsatzKW : Prop :=
  ∀ (L n : ℕ) (d : Fin (n + 1) → Fin 4) (site : Fin (n + 1) → ZMod L × ZMod L),
    (∀ k : Fin n, site k.succ = ons_dirStep L (d k.castSucc) (site k.castSucc)) →
    (∀ k : Fin n, d k.succ ≠ d k.castSucc + 2) →
    d (Fin.last n) = d 0 → site (Fin.last n) = site 0 →
    ons_SelfAvoiding site →
    ∀ m : ℤ, (∑ k : Fin n, ons_turnPow (d k.castSucc) (d k.succ)) = 4 * m → Odd m






theorem ons_propIV_of_umlaufsatz (hU : ons_DiscreteUmlaufsatzKW)
    (ω : ℂ) (hω : ω ≠ 0) (hI : ω ^ 2 = Complex.I)
    (L n : ℕ) (d : Fin (n + 1) → Fin 4) (site : Fin (n + 1) → ZMod L × ZMod L)
    (hstep : ∀ k : Fin n, site k.succ = ons_dirStep L (d k.castSucc) (site k.castSucc))
    (hnu : ∀ k : Fin n, d k.succ ≠ d k.castSucc + 2)
    (hcd : d (Fin.last n) = d 0) (hcs : site (Fin.last n) = site 0)
    (hsa : ons_SelfAvoiding site) :
    ∏ k : Fin n, ons_turnW ω (d k.castSucc) (d k.succ) = -1 := by
  obtain ⟨m, hm, _⟩ := ons_closed_walk_prod ω hω hI n d hnu hcd
  have hodd : Odd m := hU L n d site hstep hnu hcd hcs hsa m hm
  exact ons_selfAvoiding_prod ω hω hI n d hnu m hm hodd

end StatMech.Onsager
