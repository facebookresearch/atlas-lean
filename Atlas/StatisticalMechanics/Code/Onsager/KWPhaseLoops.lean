/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Code.Onsager.ShermanConvergence
import Code.Onsager.KWSpinFourier









namespace StatMech.Onsager

open Matrix BigOperators

theorem ons_loopWeight_KWmatPhase {L n : ℕ} [NeZero L] [NeZero n]
    (x omega u v : ℂ) (d : Fin n → ons_Dart L) :
    ons_loopWeight (ons_KWmatPhase L x omega u v) d =
      (∏ k, ons_dirPhase u v (d k).2) *
        ons_loopWeight (ons_KWmat L x omega) d := by
  unfold ons_loopWeight ons_KWmatPhase
  rw [Finset.prod_mul_distrib]
  congr 1
  exact Equiv.prod_comp (Equiv.addRight (1 : Fin n))
    (fun k => ons_dirPhase u v (d k).2)

theorem ons_loopWeight_KWmatPhase_zpow {L n : ℕ} [NeZero L] [NeZero n]
    (x omega u v : ℂ) (hu : u ≠ 0) (hv : v ≠ 0)
    (d : Fin n → ons_Dart L) :
    ons_loopWeight (ons_KWmatPhase L x omega u v) d =
      u ^ (∑ k, ons_dirExponentX (d k).2) *
        v ^ (∑ k, ons_dirExponentY (d k).2) *
          ons_loopWeight (ons_KWmat L x omega) d := by
  rw [ons_loopWeight_KWmatPhase,
    prod_ons_dirPhase u v hu hv (fun k => (d k).2)]

theorem ons_dirExponentX_step (L : ℕ) (mu : Fin 4)
    (p : ZMod L × ZMod L) :
    (((ons_dirExponentX mu : ℤ) : ZMod L)) =
      (ons_dirStep L mu p).1 - p.1 := by
  fin_cases mu <;> simp [ons_dirExponentX, ons_dirStep]

theorem ons_dirExponentY_step (L : ℕ) (mu : Fin 4)
    (p : ZMod L × ZMod L) :
    (((ons_dirExponentY mu : ℤ) : ZMod L)) =
      (ons_dirStep L mu p).2 - p.2 := by
  fin_cases mu <;> simp [ons_dirExponentY, ons_dirStep]

theorem ons_sum_dirExponentX_cast_zero {L n : ℕ} [NeZero L] [NeZero n]
    (d : Fin n → ons_Dart L)
    (hvalid : ∀ k : Fin n,
      (d k).1 = ons_dirStep L (d (k + 1)).2 (d (k + 1)).1) :
    (((∑ k, ons_dirExponentX (d k).2 : ℤ) : ZMod L)) = 0 := by
  rw [Int.cast_sum]
  calc
    (∑ k : Fin n, ((ons_dirExponentX (d k).2 : ℤ) : ZMod L)) =
        ∑ k : Fin n,
          ((ons_dirExponentX (d (k + 1)).2 : ℤ) : ZMod L) := by
      exact (Equiv.sum_comp (Equiv.addRight (1 : Fin n))
        (fun k => ((ons_dirExponentX (d k).2 : ℤ) : ZMod L))).symm
    _ = ∑ k : Fin n, ((d k).1.1 - (d (k + 1)).1.1) := by
      apply Finset.sum_congr rfl
      intro k _
      rw [ons_dirExponentX_step]
      rw [← hvalid k]
    _ = 0 := by
      rw [Finset.sum_sub_distrib]
      have hs : (∑ k : Fin n, (d (k + 1)).1.1) =
          ∑ k : Fin n, (d k).1.1 :=
        Equiv.sum_comp (Equiv.addRight (1 : Fin n)) (fun k => (d k).1.1)
      rw [hs, sub_self]

theorem ons_sum_dirExponentY_cast_zero {L n : ℕ} [NeZero L] [NeZero n]
    (d : Fin n → ons_Dart L)
    (hvalid : ∀ k : Fin n,
      (d k).1 = ons_dirStep L (d (k + 1)).2 (d (k + 1)).1) :
    (((∑ k, ons_dirExponentY (d k).2 : ℤ) : ZMod L)) = 0 := by
  rw [Int.cast_sum]
  calc
    (∑ k : Fin n, ((ons_dirExponentY (d k).2 : ℤ) : ZMod L)) =
        ∑ k : Fin n,
          ((ons_dirExponentY (d (k + 1)).2 : ℤ) : ZMod L) := by
      exact (Equiv.sum_comp (Equiv.addRight (1 : Fin n))
        (fun k => ((ons_dirExponentY (d k).2 : ℤ) : ZMod L))).symm
    _ = ∑ k : Fin n, ((d k).1.2 - (d (k + 1)).1.2) := by
      apply Finset.sum_congr rfl
      intro k _
      rw [ons_dirExponentY_step]
      rw [← hvalid k]
    _ = 0 := by
      rw [Finset.sum_sub_distrib]
      have hs : (∑ k : Fin n, (d (k + 1)).1.2) =
          ∑ k : Fin n, (d k).1.2 :=
        Equiv.sum_comp (Equiv.addRight (1 : Fin n)) (fun k => (d k).1.2)
      rw [hs, sub_self]



theorem ons_loop_winding_exists {L n : ℕ} [NeZero L] [NeZero n]
    (d : Fin n → ons_Dart L)
    (hvalid : ∀ k : Fin n,
      (d k).1 = ons_dirStep L (d (k + 1)).2 (d (k + 1)).1) :
    ∃ mx my : ℤ,
      (∑ k, ons_dirExponentX (d k).2) = (L : ℤ) * mx ∧
      (∑ k, ons_dirExponentY (d k).2) = (L : ℤ) * my := by
  have hx := ons_sum_dirExponentX_cast_zero d hvalid
  have hy := ons_sum_dirExponentY_cast_zero d hvalid
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hx hy
  obtain ⟨mx, hmx⟩ := hx
  obtain ⟨my, hmy⟩ := hy
  exact ⟨mx, my, hmx, hmy⟩



theorem ons_loopWeight_spinPhase {L n : ℕ} [NeZero L] [NeZero n]
    (x omega : ℂ) (a b : Fin 2) (d : Fin n → ons_Dart L)
    (hvalid : ∀ k : Fin n,
      (d k).1 = ons_dirStep L (d (k + 1)).2 (d (k + 1)).1) :
    ∃ mx my : ℤ,
      (∑ k, ons_dirExponentX (d k).2) = (L : ℤ) * mx ∧
      (∑ k, ons_dirExponentY (d k).2) = (L : ℤ) * my ∧
      ons_loopWeight (ons_KWmatPhase L x omega
          (ons_spinPhase L a) (ons_spinPhase L b)) d =
        (-1 : ℂ) ^ ((a.val : ℤ) * mx + (b.val : ℤ) * my) *
          ons_loopWeight (ons_KWmat L x omega) d := by
  obtain ⟨mx, my, hmx, hmy⟩ := ons_loop_winding_exists d hvalid
  refine ⟨mx, my, hmx, hmy, ?_⟩
  rw [ons_loopWeight_KWmatPhase_zpow x omega _ _
    (ons_spinPhase_ne_zero L a) (ons_spinPhase_ne_zero L b), hmx, hmy]
  have ha : ons_spinPhase L a ^ (L : ℤ) =
      (-1 : ℂ) ^ (a.val : ℤ) := by
    rw [zpow_natCast]
    rw [zpow_natCast]
    exact ons_spinPhase_pow_side L a
  have hb : ons_spinPhase L b ^ (L : ℤ) =
      (-1 : ℂ) ^ (b.val : ℤ) := by
    rw [zpow_natCast]
    rw [zpow_natCast]
    exact ons_spinPhase_pow_side L b
  rw [_root_.zpow_mul, _root_.zpow_mul, ha, hb,
    ← _root_.zpow_mul, ← _root_.zpow_mul,
    ← zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0)]

@[simp] theorem ons_dirExponentX_opposite (mu : Fin 4) :
    ons_dirExponentX (mu + 2) = -ons_dirExponentX mu := by
  fin_cases mu <;> rfl

@[simp] theorem ons_dirExponentY_opposite (mu : Fin 4) :
    ons_dirExponentY (mu + 2) = -ons_dirExponentY mu := by
  fin_cases mu <;> rfl

theorem ons_loopRev_sum_dirExponentX {L n : ℕ} [NeZero n]
    (d : Fin n → ons_Dart L) :
    ∑ k, ons_dirExponentX ((ons_loopRev L d k).2) =
      -∑ k, ons_dirExponentX ((d k).2) := by
  simp only [ons_loopRev, ons_dartRev,
    ons_dirExponentX_opposite]
  rw [← Finset.sum_neg_distrib]
  exact Equiv.sum_comp (Equiv.neg (Fin n))
    (fun k => -ons_dirExponentX (d k).2)

theorem ons_loopRev_sum_dirExponentY {L n : ℕ} [NeZero n]
    (d : Fin n → ons_Dart L) :
    ∑ k, ons_dirExponentY ((ons_loopRev L d k).2) =
      -∑ k, ons_dirExponentY ((d k).2) := by
  simp only [ons_loopRev, ons_dartRev,
    ons_dirExponentY_opposite]
  rw [← Finset.sum_neg_distrib]
  exact Equiv.sum_comp (Equiv.neg (Fin n))
    (fun k => -ons_dirExponentY (d k).2)



theorem ons_loopWeight_spinPhase_loopRev
    {L n : ℕ} [NeZero L] [NeZero n]
    (x omega : ℂ) (homega : omega ^ 2 = Complex.I)
    (a b : Fin 2) (d : Fin n → ons_Dart L) :
    ons_loopWeight (ons_KWmatPhase L x omega
        (ons_spinPhase L a) (ons_spinPhase L b)) (ons_loopRev L d) =
      ons_loopWeight (ons_KWmatPhase L x omega
        (ons_spinPhase L a) (ons_spinPhase L b)) d := by
  by_cases hvalid : ∀ k : Fin n,
      (d k).1 = ons_dirStep L (d (k + 1)).2 (d (k + 1)).1
  · obtain ⟨mx, my, hmx, hmy⟩ := ons_loop_winding_exists d hvalid
    have ha : ons_spinPhase L a ^ (L : ℤ) =
        (-1 : ℂ) ^ (a.val : ℤ) := by
      rw [zpow_natCast, zpow_natCast]
      exact ons_spinPhase_pow_side L a
    have hb : ons_spinPhase L b ^ (L : ℤ) =
        (-1 : ℂ) ^ (b.val : ℤ) := by
      rw [zpow_natCast, zpow_natCast]
      exact ons_spinPhase_pow_side L b
    rw [ons_loopWeight_KWmatPhase_zpow x omega _ _
        (ons_spinPhase_ne_zero L a) (ons_spinPhase_ne_zero L b),
      ons_loopWeight_KWmatPhase_zpow x omega _ _
        (ons_spinPhase_ne_zero L a) (ons_spinPhase_ne_zero L b),
      ons_loopRev_sum_dirExponentX, ons_loopRev_sum_dirExponentY,
      hmx, hmy, show -((L : ℤ) * mx) = (L : ℤ) * (-mx) by ring,
      show -((L : ℤ) * my) = (L : ℤ) * (-my) by ring,
      _root_.zpow_mul, _root_.zpow_mul, _root_.zpow_mul,
      _root_.zpow_mul, ha, hb,
      ons_loopWeight_loopRev x omega homega d]
    have hinvneg (m : ℤ) : (((-1 : ℂ) ^ m)⁻¹ = (-1 : ℂ) ^ m) := by
      rcases Int.even_or_odd m with hm | hm
      · rw [hm.neg_one_zpow]
        simp
      · rw [hm.neg_one_zpow]
        simp
    have hpow (c : Fin 2) (m : ℤ) :
        ((-1 : ℂ) ^ (c.val : ℤ)) ^ (-m) =
          ((-1 : ℂ) ^ (c.val : ℤ)) ^ m := by
      fin_cases c
      · simp
      · simp only [Nat.cast_one, zpow_one,
          _root_.zpow_neg]
        exact hinvneg m
    rw [hpow a mx, hpow b my]
  · push Not at hvalid
    obtain ⟨k, hk⟩ := hvalid
    have hzero : ons_loopWeight (ons_KWmat L x omega) d = 0 := by
      unfold ons_loopWeight
      apply Finset.prod_eq_zero (Finset.mem_univ k)
      simp only [ons_KWmat]
      exact if_neg hk
    rw [ons_loopWeight_KWmatPhase, ons_loopWeight_KWmatPhase,
      hzero, ons_loopWeight_loopRev x omega homega d, hzero]
    ring

theorem ons_loopRev_hits_iff
    {L n : ℕ} [NeZero n] (forbidden : Finset (ons_Dart L))
    (hforbidden : ∀ d,
      ons_dartRev L d ∈ forbidden ↔ d ∈ forbidden)
    (d : Fin n → ons_Dart L) :
    (∃ k, ons_loopRev L d k ∈ forbidden) ↔
      ∃ k, d k ∈ forbidden := by
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨-k, ?_⟩
    exact (hforbidden _).mp hk
  · rintro ⟨k, hk⟩
    refine ⟨-k, ?_⟩
    change ons_dartRev L (d (-(-k))) ∈ forbidden
    rw [neg_neg]
    exact (hforbidden _).mpr hk

theorem ons_loopWeight_spinPhase_mask_loopRev
    {L n : ℕ} [NeZero L] [NeZero n]
    (x omega : ℂ) (homega : omega ^ 2 = Complex.I)
    (a b : Fin 2) (forbidden : Finset (ons_Dart L))
    (hforbidden : ∀ d,
      ons_dartRev L d ∈ forbidden ↔ d ∈ forbidden)
    (d : Fin n → ons_Dart L) :
    ons_loopWeight
        (ons_maskMatrix forbidden (ons_KWmatPhase L x omega
          (ons_spinPhase L a) (ons_spinPhase L b))) (ons_loopRev L d) =
      ons_loopWeight
        (ons_maskMatrix forbidden (ons_KWmatPhase L x omega
          (ons_spinPhase L a) (ons_spinPhase L b))) d := by
  have hhit := ons_loopRev_hits_iff forbidden hforbidden d
  rw [ons_loopWeight_maskMatrix, ons_loopWeight_maskMatrix]
  by_cases h : ∃ k, d k ∈ forbidden
  · rw [if_pos h, if_pos (hhit.mpr h)]
  · rw [if_neg h, if_neg (fun hr => h (hhit.mp hr))]
    exact ons_loopWeight_spinPhase_loopRev x omega homega a b d



theorem ons_loopSum_spinPhase_symm
    {L n : ℕ} [NeZero L] [NeZero n]
    (x omega : ℂ) (homega : omega ^ 2 = Complex.I)
    (a b : Fin 2) (e : ons_Dart L) :
    (∑ d ∈ (Finset.univ.filter (fun d : Fin n → ons_Dart L =>
        (∃ i, d i = e) ∧ ¬ ∃ j, d j = ons_dartRev L e)),
        ons_loopWeight (ons_KWmatPhase L x omega
          (ons_spinPhase L a) (ons_spinPhase L b)) d) =
      ∑ d ∈ (Finset.univ.filter (fun d : Fin n → ons_Dart L =>
        (∃ i, d i = ons_dartRev L e) ∧ ¬ ∃ j, d j = e)),
        ons_loopWeight (ons_KWmatPhase L x omega
          (ons_spinPhase L a) (ons_spinPhase L b)) d := by
  refine Finset.sum_nbij' (ons_loopRev L) (ons_loopRev L) ?_ ?_ ?_ ?_ ?_
  · intro d hd
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hd ⊢
    obtain ⟨⟨i, hie⟩, hne⟩ := hd
    constructor
    · rw [ons_visits_loopRev, ons_dartRev_involutive L e]
      exact ⟨i, hie⟩
    · rwa [ons_visits_loopRev]
  · intro d hd
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hd ⊢
    obtain ⟨⟨i, hie⟩, hne⟩ := hd
    constructor
    · rw [ons_visits_loopRev]
      exact ⟨i, hie⟩
    · rwa [ons_visits_loopRev, ons_dartRev_involutive L e]
  · exact fun d _ => ons_loopRev_involutive L n d
  · exact fun d _ => ons_loopRev_involutive L n d
  · intro d _
    exact (ons_loopWeight_spinPhase_loopRev x omega homega a b d).symm

theorem ons_loopSum_spinPhase_mask_symm
    {L n : ℕ} [NeZero L] [NeZero n]
    (x omega : ℂ) (homega : omega ^ 2 = Complex.I)
    (a b : Fin 2) (forbidden : Finset (ons_Dart L))
    (hforbidden : ∀ d,
      ons_dartRev L d ∈ forbidden ↔ d ∈ forbidden)
    (e : ons_Dart L) :
    (∑ d ∈ (Finset.univ.filter (fun d : Fin n → ons_Dart L =>
        (∃ i, d i = e) ∧ ¬ ∃ j, d j = ons_dartRev L e)),
        ons_loopWeight
          (ons_maskMatrix forbidden (ons_KWmatPhase L x omega
            (ons_spinPhase L a) (ons_spinPhase L b))) d) =
      ∑ d ∈ (Finset.univ.filter (fun d : Fin n → ons_Dart L =>
        (∃ i, d i = ons_dartRev L e) ∧ ¬ ∃ j, d j = e)),
        ons_loopWeight
          (ons_maskMatrix forbidden (ons_KWmatPhase L x omega
            (ons_spinPhase L a) (ons_spinPhase L b))) d := by
  refine Finset.sum_nbij' (ons_loopRev L) (ons_loopRev L) ?_ ?_ ?_ ?_ ?_
  · intro d hd
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hd ⊢
    obtain ⟨⟨i, hie⟩, hne⟩ := hd
    constructor
    · rw [ons_visits_loopRev, ons_dartRev_involutive L e]
      exact ⟨i, hie⟩
    · rwa [ons_visits_loopRev]
  · intro d hd
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hd ⊢
    obtain ⟨⟨i, hie⟩, hne⟩ := hd
    constructor
    · rw [ons_visits_loopRev]
      exact ⟨i, hie⟩
    · rwa [ons_visits_loopRev, ons_dartRev_involutive L e]
  · exact fun d _ => ons_loopRev_involutive L n d
  · exact fun d _ => ons_loopRev_involutive L n d
  · intro d _
    exact (ons_loopWeight_spinPhase_mask_loopRev
      x omega homega a b forbidden hforbidden d).symm

theorem norm_ons_KWmatPhase_spin_entry_le (L : ℕ) (x : ℝ)
    (a b : Fin 2) (d2 d1 : ons_Dart L) :
    ‖ons_KWmatPhase L (x : ℂ) ons_turnRoot
      (ons_spinPhase L a) (ons_spinPhase L b) d2 d1‖ ≤ ‖(x : ℂ)‖ := by
  exact_mod_cast nnnorm_ons_KWmatPhase_le L x a b d2 d1

theorem ons_KWmatPhase_firstReturnWeight_small
    (L : ℕ) [NeZero L]
    {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) (ons_ShermanRadius L))
    (a b : Fin 2) (e r : ons_Dart L) :
    Summable (fun s =>
      ‖ons_firstReturnWeight
        (ons_KWmatPhase L (x : ℂ) ons_turnRoot
          (ons_spinPhase L a) (ons_spinPhase L b)) e r s‖) ∧
      (∑' s, ‖ons_firstReturnWeight
        (ons_KWmatPhase L (x : ℂ) ons_turnRoot
          (ons_spinPhase L a) (ons_spinPhase L b)) e r s‖) < 1 := by
  apply ons_firstReturnWeight_small _ e r ‖(x : ℂ)‖ (norm_nonneg _)
    (norm_ons_KWmatPhase_spin_entry_le L x a b)
  simpa [ons_ShermanRadius, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hx.1] using hx.2

theorem ons_KWmatPhase_filteredLoopSeries_summable
    (L : ℕ) [NeZero L]
    {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) (ons_ShermanRadius L))
    (a b : Fin 2)
    (P : (n : ℕ) → (Fin (n + 1) → ons_Dart L) → Prop)
    [∀ n, DecidablePred (P n)] :
    Summable fun n : ℕ =>
      (∑ d ∈ Finset.univ.filter (P n),
        ons_loopWeight
          (ons_KWmatPhase L (x : ℂ) ons_turnRoot
            (ons_spinPhase L a) (ons_spinPhase L b)) d) / ((n : ℂ) + 1) := by
  apply ons_summable_filteredLoopSeries _ ‖(x : ℂ)‖ (norm_nonneg _)
    (norm_ons_KWmatPhase_spin_entry_le L x a b)
  simpa [Complex.norm_real] using ons_Sherman_card_mul_small L hx

end StatMech.Onsager
