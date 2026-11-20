/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Code.Onsager.KWMatrix






















namespace StatMech.Onsager




def ons_dartRev (L : ℕ) (d : ons_Dart L) : ons_Dart L :=
  (ons_dirStep L d.2 d.1, d.2 + 2)



theorem ons_dirStep_opposite (L : ℕ) (μ : Fin 4) (p : ZMod L × ZMod L) :
    ons_dirStep L (μ + 2) (ons_dirStep L μ p) = p := by
  fin_cases μ <;> simp [ons_dirStep]


theorem ons_dartRev_involutive (L : ℕ) : Function.Involutive (ons_dartRev L) := by
  intro d
  obtain ⟨p, μ⟩ := d
  simp only [ons_dartRev]
  rw [Prod.mk.injEq]
  refine ⟨?_, ?_⟩
  · exact ons_dirStep_opposite L μ p
  · fin_cases μ <;> decide


theorem ons_dartRev_ne (L : ℕ) [Fact (2 < L)] (d : ons_Dart L) :
    ons_dartRev L d ≠ d := by
  obtain ⟨p, μ⟩ := d
  intro hcontra
  have h2 : (ons_dartRev L (p, μ)).2 = μ := congrArg Prod.snd hcontra
  simp only [ons_dartRev] at h2
  revert h2
  fin_cases μ <;> decide





def ons_turnZ (μ ν : Fin 4) : ZMod 4 := (ν : ZMod 4) - (μ : ZMod 4)


theorem ons_turnZ_telescope (n : ℕ) (d : Fin (n + 1) → Fin 4) :
    (∑ k : Fin n, ((d k.succ : ZMod 4) - (d k.castSucc : ZMod 4)))
      = (d (Fin.last n) : ZMod 4) - (d 0 : ZMod 4) := by
  
  set F : ℕ → ZMod 4 := fun i => if h : i < n + 1 then (d ⟨i, h⟩ : ZMod 4) else 0 with hF
  have hFval : ∀ (i : ℕ) (hi : i < n + 1), F i = (d ⟨i, hi⟩ : ZMod 4) := by
    intro i hi; simp only [hF, dif_pos hi]
  have hsucc : ∀ k : Fin n, (d k.succ : ZMod 4) = F (k.val + 1) := by
    intro k
    have hk : k.val + 1 < n + 1 := by omega
    have he : k.succ = (⟨k.val + 1, hk⟩ : Fin (n + 1)) := by ext; simp
    rw [hFval (k.val + 1) hk, he]
  have hcast : ∀ k : Fin n, (d k.castSucc : ZMod 4) = F k.val := by
    intro k
    have hk : k.val < n + 1 := by omega
    have he : k.castSucc = (⟨k.val, hk⟩ : Fin (n + 1)) := by ext; simp
    rw [hFval k.val hk, he]
  have hstep : (∑ k : Fin n, ((d k.succ : ZMod 4) - (d k.castSucc : ZMod 4)))
      = ∑ k : Fin n, (F (k.val + 1) - F k.val) := by
    apply Finset.sum_congr rfl
    intro k _
    rw [hsucc k, hcast k]
    rfl
  have heN : (Fin.last n) = (⟨n, Nat.lt_succ_self n⟩ : Fin (n + 1)) := by ext; simp
  have he0 : (0 : Fin (n + 1)) = (⟨0, Nat.succ_pos n⟩ : Fin (n + 1)) := by ext; simp
  rw [hstep, Fin.sum_univ_eq_sum_range (fun i => F (i + 1) - F i) n,
    Finset.sum_range_sub F n, hFval n (Nat.lt_succ_self n), hFval 0 (Nat.succ_pos n),
    heN, he0]
  rfl






def ons_turnPow (μ ν : Fin 4) : ℤ :=
  if ν = μ then 0 else if ν = μ + 1 then 1 else if ν = μ + 2 then 0 else -1


theorem ons_turnW_eq_zpow (ω : ℂ) (μ ν : Fin 4) (h : ν ≠ μ + 2) :
    ons_turnW ω μ ν = ω ^ (ons_turnPow μ ν) := by
  unfold ons_turnW ons_turnPow
  by_cases h0 : ν = μ
  · simp [h0]
  · by_cases h1 : ν = μ + 1
    · simp [h1]
    · rw [if_neg h0, if_neg h1, if_neg h, if_neg h0, if_neg h1, if_neg h]
      simp


theorem ons_prod_zpow (ω : ℂ) (hω : ω ≠ 0) {ι : Type*} (s : Finset ι) (f : ι → ℤ) :
    ∏ i ∈ s, ω ^ (f i) = ω ^ (∑ i ∈ s, f i) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp
  · intro a s ha ih
    rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, ← zpow_add₀ hω]



theorem ons_turnPow_cast (μ ν : Fin 4) (h : ν ≠ μ + 2) :
    ((ons_turnPow μ ν : ℤ) : ZMod 4) = ons_turnZ μ ν := by
  revert h
  fin_cases μ <;> fin_cases ν <;> decide


theorem ons_walk_prod_eq (ω : ℂ) (hω : ω ≠ 0) (n : ℕ) (d : Fin (n + 1) → Fin 4)
    (hnu : ∀ k : Fin n, d k.succ ≠ d k.castSucc + 2) :
    ∏ k : Fin n, ons_turnW ω (d k.castSucc) (d k.succ)
      = ω ^ (∑ k : Fin n, ons_turnPow (d k.castSucc) (d k.succ)) := by
  rw [← ons_prod_zpow ω hω]
  apply Finset.prod_congr rfl
  intro k _
  exact ons_turnW_eq_zpow ω (d k.castSucc) (d k.succ) (hnu k)



theorem ons_walk_turnPow_mod (n : ℕ) (d : Fin (n + 1) → Fin 4)
    (hnu : ∀ k : Fin n, d k.succ ≠ d k.castSucc + 2) :
    ((∑ k : Fin n, ons_turnPow (d k.castSucc) (d k.succ) : ℤ) : ZMod 4)
      = (d (Fin.last n) : ZMod 4) - (d 0 : ZMod 4) := by
  rw [Int.cast_sum, ← ons_turnZ_telescope n d]
  apply Finset.sum_congr rfl
  intro k _
  rw [ons_turnPow_cast (d k.castSucc) (d k.succ) (hnu k)]
  rfl





theorem ons_omega_pow_four (ω : ℂ) (h : ω ^ 2 = Complex.I) : ω ^ 4 = -1 := by
  have h4 : ω ^ 4 = (ω ^ 2) ^ 2 := by ring
  rw [h4, h, Complex.I_sq]





theorem ons_walk_prod_antipodal (ω : ℂ) (hω : ω ≠ 0) (hI : ω ^ 2 = Complex.I)
    (n : ℕ) (d : Fin (n + 1) → Fin 4)
    (hnu : ∀ k : Fin n, d k.succ ≠ d k.castSucc + 2)
    (hend : d (Fin.last n) = d 0 + 2) :
    ∃ m : ℤ, ∏ k : Fin n, ons_turnW ω (d k.castSucc) (d k.succ)
      = (-1) ^ m * Complex.I := by
  
  have hmod : ((∑ k : Fin n, ons_turnPow (d k.castSucc) (d k.succ) : ℤ) : ZMod 4) = 2 := by
    rw [ons_walk_turnPow_mod n d hnu, hend]
    generalize d 0 = a
    fin_cases a <;> rfl
  
  obtain ⟨m, hm⟩ : ∃ m : ℤ,
      (∑ k : Fin n, ons_turnPow (d k.castSucc) (d k.succ)) = 4 * m + 2 := by
    have hzero : (((∑ k : Fin n, ons_turnPow (d k.castSucc) (d k.succ)) - 2 : ℤ)
        : ZMod 4) = 0 := by
      rw [Int.cast_sub, hmod]
      decide
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hzero
    obtain ⟨k, hk⟩ := hzero
    exact ⟨k, by push_cast at hk; linarith⟩
  refine ⟨m, ?_⟩
  rw [ons_walk_prod_eq ω hω n d hnu, hm, zpow_add₀ hω, zpow_mul]
  have h4 : ω ^ (4 : ℤ) = -1 := by
    rw [show (4 : ℤ) = ((4 : ℕ) : ℤ) from rfl, zpow_natCast]
    exact ons_omega_pow_four ω hI
  have h2 : ω ^ (2 : ℤ) = Complex.I := by
    rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast]
    exact hI
  rw [h4, h2]

end StatMech.Onsager
