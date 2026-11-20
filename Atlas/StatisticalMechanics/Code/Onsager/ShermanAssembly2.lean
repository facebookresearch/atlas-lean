/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Code.Onsager.KWLoopWeight
import Code.Onsager.ShermanAssembly1

















































namespace StatMech.Onsager

open Matrix BigOperators Finset




theorem ons_turnW_omega_inv (ω : ℂ) (μ ν : Fin 4) :
    ons_turnW ω⁻¹ μ ν = (ons_turnW ω μ ν)⁻¹ := by
  unfold ons_turnW
  split_ifs <;> simp










theorem ons_KWmat_dartRev (L : ℕ) (x ω : ℂ) (d₁ d₂ : ons_Dart L) :
    ons_KWmat L x ω (ons_dartRev L d₁) (ons_dartRev L d₂)
      = ons_KWmat L x ω⁻¹ d₂ d₁ := by
  obtain ⟨p₁, μ₁⟩ := d₁
  obtain ⟨p₂, μ₂⟩ := d₂
  simp only [ons_KWmat, ons_dartRev, ons_dirStep_opposite]
  rw [ons_turnW_rev ω μ₁ μ₂, ons_turnW_omega_inv]
  by_cases h : ons_dirStep L μ₁ p₁ = p₂
  · rw [if_pos h, if_pos h.symm]
  · rw [if_neg h, if_neg (fun hc => h hc.symm)]





def ons_loopRev (L : ℕ) {n : ℕ} [NeZero n] (v : Fin n → ons_Dart L) : Fin n → ons_Dart L :=
  fun k => ons_dartRev L (v (-k))


theorem ons_loopRev_involutive (L n : ℕ) [NeZero n] (v : Fin n → ons_Dart L) :
    ons_loopRev L (ons_loopRev L v) = v := by
  funext k
  simp only [ons_loopRev, neg_neg]
  exact ons_dartRev_involutive L (v k)


theorem ons_visits_loopRev {L n : ℕ} [NeZero n] (v : Fin n → ons_Dart L) (d : ons_Dart L) :
    (∃ i, ons_loopRev L v i = d) ↔ (∃ i, v i = ons_dartRev L d) := by
  unfold ons_loopRev
  constructor
  · rintro ⟨i, hi⟩
    refine ⟨-i, ?_⟩
    have h := congrArg (ons_dartRev L) hi
    rwa [ons_dartRev_involutive L (v (-i))] at h
  · rintro ⟨i, hi⟩
    refine ⟨-i, ?_⟩
    rw [neg_neg, hi, ons_dartRev_involutive L d]








theorem ons_loopWeight_dartRev {L n : ℕ} [NeZero L] [NeZero n] (x ω : ℂ)
    (v : Fin n → ons_Dart L) :
    ons_loopWeight (ons_KWmat L x ω) (fun k => ons_dartRev L (v (-k)))
      = ons_loopWeight (ons_KWmat L x ω⁻¹) v := by
  unfold ons_loopWeight
  have step1 : (∏ k : Fin n, ons_KWmat L x ω (ons_dartRev L (v (-k)))
        (ons_dartRev L (v (-(k + 1)))))
      = ∏ k : Fin n, ons_KWmat L x ω⁻¹ (v (-(k + 1))) (v (-k)) := by
    apply Finset.prod_congr rfl
    intro k _
    exact ons_KWmat_dartRev L x ω (v (-k)) (v (-(k + 1)))
  rw [step1]
  rw [← Equiv.prod_comp ((Equiv.addRight (1 : Fin n)).trans (Equiv.neg (Fin n)))
      (fun j => ons_KWmat L x ω⁻¹ (v j) (v (j + 1)))]
  apply Finset.prod_congr rfl
  intro k _
  have hρ : ((Equiv.addRight (1 : Fin n)).trans (Equiv.neg (Fin n))) k = -(k + 1) := rfl
  rw [hρ]
  have hk1 : (-(k + 1) + 1 : Fin n) = -k := by abel
  rw [hk1]








theorem ons_loopWeight_omega_inv {L n : ℕ} [NeZero L] [NeZero n] (x ω : ℂ)
    (hω0 : ω ≠ 0) (hI : ω ^ 2 = Complex.I) (v : Fin n → ons_Dart L) :
    ons_loopWeight (ons_KWmat L x ω⁻¹) v = ons_loopWeight (ons_KWmat L x ω) v := by
  by_cases hvalid : ∀ k : Fin n, (v k).1 = ons_dirStep L (v (k + 1)).2 (v (k + 1)).1
  · rw [ons_loopWeight_KW_eq x ω⁻¹ v hvalid, ons_loopWeight_KW_eq x ω v hvalid]
    congr 1
    by_cases hu : ∃ k : Fin n, (v k).2 = (v (k + 1)).2 + 2
    · obtain ⟨k, hk⟩ := hu
      have z1 : ons_turnW ω⁻¹ (v (k + 1)).2 (v k).2 = 0 := by
        rw [hk]; exact ons_turnW_uturn ω⁻¹ _
      have z2 : ons_turnW ω (v (k + 1)).2 (v k).2 = 0 := by
        rw [hk]; exact ons_turnW_uturn ω _
      rw [Finset.prod_eq_zero (Finset.mem_univ k) z1,
        Finset.prod_eq_zero (Finset.mem_univ k) z2]
    · push_neg at hu
      have hnu : ∀ k : Fin n, (v k).2 ≠ (v (k + 1)).2 + 2 := hu
      have hpω : (∏ k : Fin n, ons_turnW ω (v (k + 1)).2 (v k).2)
          = ω ^ (∑ k : Fin n, ons_turnPow (v (k + 1)).2 (v k).2) := by
        rw [← ons_prod_zpow ω hω0]
        exact Finset.prod_congr rfl (fun k _ => ons_turnW_eq_zpow ω _ _ (hnu k))
      have hpωi : (∏ k : Fin n, ons_turnW ω⁻¹ (v (k + 1)).2 (v k).2)
          = ω⁻¹ ^ (∑ k : Fin n, ons_turnPow (v (k + 1)).2 (v k).2) := by
        rw [← ons_prod_zpow ω⁻¹ (inv_ne_zero hω0)]
        exact Finset.prod_congr rfl (fun k _ => ons_turnW_eq_zpow ω⁻¹ _ _ (hnu k))
      rw [hpω, hpωi]
      set S := ∑ k : Fin n, ons_turnPow (v (k + 1)).2 (v k).2 with hS
      have hScast : ((S : ℤ) : ZMod 4) = 0 := by
        have hterm : ∀ k : Fin n,
            (((ons_turnPow (v (k + 1)).2 (v k).2 : ℤ)) : ZMod 4)
              = ((v k).2 : ZMod 4) - ((v (k + 1)).2 : ZMod 4) := by
          intro k
          rw [ons_turnPow_cast _ _ (hnu k)]
          rfl
        have hshift : (∑ k : Fin n, ((v (k + 1)).2 : ZMod 4))
            = ∑ k : Fin n, ((v k).2 : ZMod 4) :=
          Equiv.sum_comp (Equiv.addRight (1 : Fin n)) (fun k => ((v k).2 : ZMod 4))
        rw [hS, Int.cast_sum]
        calc (∑ k : Fin n, ((ons_turnPow (v (k + 1)).2 (v k).2 : ℤ) : ZMod 4))
            = ∑ k : Fin n, (((v k).2 : ZMod 4) - ((v (k + 1)).2 : ZMod 4)) :=
              Finset.sum_congr rfl (fun k _ => hterm k)
          _ = (∑ k : Fin n, ((v k).2 : ZMod 4)) - ∑ k : Fin n, ((v (k + 1)).2 : ZMod 4) := by
              rw [Finset.sum_sub_distrib]
          _ = 0 := by rw [hshift, sub_self]
      obtain ⟨m, hm⟩ : ∃ m : ℤ, S = 4 * m := by
        obtain ⟨m, hm⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd S 4).mp hScast
        exact ⟨m, by exact_mod_cast hm⟩
      have h4 : ω ^ (4 : ℤ) = -1 := by
        rw [show (4 : ℤ) = ((4 : ℕ) : ℤ) from rfl, zpow_natCast]
        exact ons_omega_pow_four ω hI
      rw [hm, _root_.zpow_mul, _root_.zpow_mul, _root_.inv_zpow, h4]
      simp
  · push_neg at hvalid
    obtain ⟨k, hk⟩ := hvalid
    unfold ons_loopWeight
    have e1 : ons_KWmat L x ω⁻¹ (v k) (v (k + 1)) = 0 := by
      simp only [ons_KWmat]; exact if_neg hk
    have e2 : ons_KWmat L x ω (v k) (v (k + 1)) = 0 := by
      simp only [ons_KWmat]; exact if_neg hk
    rw [Finset.prod_eq_zero (Finset.mem_univ k) e1,
      Finset.prod_eq_zero (Finset.mem_univ k) e2]




theorem ons_loopWeight_loopRev {L n : ℕ} [NeZero L] [NeZero n] (x ω : ℂ)
    (hI : ω ^ 2 = Complex.I) (v : Fin n → ons_Dart L) :
    ons_loopWeight (ons_KWmat L x ω) (ons_loopRev L v)
      = ons_loopWeight (ons_KWmat L x ω) v := by
  have hω0 : ω ≠ 0 := by
    rintro rfl
    rw [zero_pow (by norm_num : (2 : ℕ) ≠ 0)] at hI
    exact Complex.I_ne_zero hI.symm
  have hrev : ons_loopRev L v = (fun k => ons_dartRev L (v (-k))) := rfl
  rw [hrev, ons_loopWeight_dartRev x ω v]
  exact ons_loopWeight_omega_inv x ω hω0 hI v








theorem ons_loopSum_symm_omega_inv {L : ℕ} [NeZero L] {n : ℕ} [NeZero n] (x ω : ℂ)
    (e : ons_Dart L) :
    (∑ v ∈ (Finset.univ.filter (fun v : Fin n → ons_Dart L =>
        (∃ i, v i = e) ∧ ¬ ∃ j, v j = ons_dartRev L e)),
        ons_loopWeight (ons_KWmat L x ω) v)
      = ∑ v ∈ (Finset.univ.filter (fun v : Fin n → ons_Dart L =>
        (∃ i, v i = ons_dartRev L e) ∧ ¬ ∃ j, v j = e)),
        ons_loopWeight (ons_KWmat L x ω⁻¹) v := by
  refine Finset.sum_nbij' (ons_loopRev L) (ons_loopRev L) ?_ ?_ ?_ ?_ ?_
  · 
    intro v hv
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
    obtain ⟨⟨i, hie⟩, hne⟩ := hv
    refine ⟨?_, ?_⟩
    · rw [ons_visits_loopRev, ons_dartRev_involutive L e]
      exact ⟨i, hie⟩
    · rw [ons_visits_loopRev]
      exact hne
  · 
    intro w hw
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
    obtain ⟨⟨i, hie⟩, hne⟩ := hw
    refine ⟨?_, ?_⟩
    · rw [ons_visits_loopRev]
      exact ⟨i, hie⟩
    · rw [ons_visits_loopRev, ons_dartRev_involutive L e]
      exact hne
  · exact fun v _ => ons_loopRev_involutive L n v
  · exact fun w _ => ons_loopRev_involutive L n w
  · 
    intro v _
    have hrev : ons_loopRev L v = (fun k => ons_dartRev L (v (-k))) := rfl
    rw [hrev, ons_loopWeight_dartRev x ω⁻¹ v, inv_inv]










theorem ons_loopSum_symm {L : ℕ} [NeZero L] {n : ℕ} [NeZero n] (x ω : ℂ)
    (hω : ω ^ 2 = Complex.I) (e : ons_Dart L) :
    (∑ v ∈ (Finset.univ.filter (fun v : Fin n → ons_Dart L =>
        (∃ i, v i = e) ∧ ¬ ∃ j, v j = ons_dartRev L e)),
        ons_loopWeight (ons_KWmat L x ω) v)
      = ∑ v ∈ (Finset.univ.filter (fun v : Fin n → ons_Dart L =>
        (∃ i, v i = ons_dartRev L e) ∧ ¬ ∃ j, v j = e)),
        ons_loopWeight (ons_KWmat L x ω) v := by
  refine Finset.sum_nbij' (ons_loopRev L) (ons_loopRev L) ?_ ?_ ?_ ?_ ?_
  · intro v hv
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
    obtain ⟨⟨i, hie⟩, hne⟩ := hv
    refine ⟨?_, ?_⟩
    · rw [ons_visits_loopRev, ons_dartRev_involutive L e]
      exact ⟨i, hie⟩
    · rw [ons_visits_loopRev]
      exact hne
  · intro w hw
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
    obtain ⟨⟨i, hie⟩, hne⟩ := hw
    refine ⟨?_, ?_⟩
    · rw [ons_visits_loopRev]
      exact ⟨i, hie⟩
    · rw [ons_visits_loopRev, ons_dartRev_involutive L e]
      exact hne
  · exact fun v _ => ons_loopRev_involutive L n v
  · exact fun w _ => ons_loopRev_involutive L n w
  · intro v _
    exact (ons_loopWeight_loopRev x ω hω v).symm

end StatMech.Onsager
