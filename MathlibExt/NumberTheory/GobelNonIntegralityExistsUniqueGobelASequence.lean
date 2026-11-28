/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.GobelBSequence
import Mathlib.Algebra.Ring.Periodic
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Existence and uniqueness of the Göbel sign sequence `a_{p,l}`

The defining symmetries of `a_{p,l}` determine exactly one function `ℕ → ℤ`.
The proof restricts the periodic sequence `b_{l,s}` with `(p-1)/2 ≡ s`.

Source: Yuh Kobayashi and Shin-ichiro Seki, *A Note on Non-Integrality of the (k, l)-Göbel
Sequences*, Journal of Integer Sequences 29 (2026), Article 26.3.8, Proposition 17.
-/

namespace MetaMathlibExt
namespace existsUnique_gobelASequence

private noncomputable def extendA (l : ℕ) (a : ℕ → ℤ) (n : ℤ) : ℤ :=
  let r := n % (l + 1 : ℤ)
  if r = 0 then a (l + 1) else a r.toNat

private theorem s_facts (p l : ℕ) (hp : p.Prime) (hmod : p % 4 = 1) (hl : l ≤ p - 3) :
    ((p - 1) / 2) % (l + 1) ≤ l ∧
    (2 * (((p - 1) / 2) % (l + 1)) + 1) % (l + 1) = p % (l + 1) ∧
    Nat.Coprime (2 * (((p - 1) / 2) % (l + 1)) + 1) (l + 1) := by
  set s := ((p - 1) / 2) % (l + 1) with hs
  set Q := ((p - 1) / 2) / (l + 1) with hQ
  have hp2 := hp.two_le
  have hMpos : 0 < l + 1 := by omega
  have hslt : s < l + 1 := hs ▸ Nat.mod_lt _ hMpos
  have hsle : s ≤ l := by omega
  have h2X : 2 * ((p - 1) / 2) + 1 = p := by omega
  have hcp : Nat.Coprime p (l + 1) :=
    Nat.coprime_of_lt_prime (by omega) (by omega) hp
  have hmod : (2 * s + 1) % (l + 1) = p % (l + 1) := by
    have hdiv := Nat.div_add_mod ((p - 1) / 2) (l + 1)
    rw [← hQ, ← hs] at hdiv
    have hX : (p - 1) / 2 = (l + 1) * Q + s := hdiv.symm
    have hEq : 2 * ((p - 1) / 2) + 1 = (2 * s + 1) + (l + 1) * (2 * Q) := by
      rw [hX]; ring
    have h1 : (2 * ((p - 1) / 2) + 1) % (l + 1) = (2 * s + 1) % (l + 1) := by
      rw [hEq, Nat.add_mul_mod_self_left]
    rw [h2X] at h1
    exact h1.symm
  have hcop : Nat.Coprime (2 * s + 1) (l + 1) := by
    have e1 := ZMod.coprime_mod_iff_coprime (2 * s + 1) (l + 1)
    have e2 := ZMod.coprime_mod_iff_coprime p (l + 1)
    rw [hmod] at e1
    exact e1.mp (e2.mpr hcp)
  exact ⟨hsle, hmod, hcop⟩

private theorem exists_a_of_b (p l s : ℕ) (hp : p.Prime) (hmod : p % 4 = 1)
    (hl : l ≤ p - 3)
    (hcong : (2 * s + 1) % (l + 1) = p % (l + 1))
    (b : ℤ → ℤ) (hb : IsGobelBSequence l s b) :
    ∃ a : ℕ → ℤ, IsGobelASequence p l a ∧ ∀ n, 1 ≤ n → n ≤ p - 1 → a n = b (n : ℤ) := by
  have hp2 := hp.two_le
  have h5 : 5 ≤ p := by omega
  let a : ℕ → ℤ := fun n => if n = 0 ∨ p ≤ n then 0 else b (n : ℤ)
  have ha_eq (n : ℕ) (h : ¬(n = 0 ∨ p ≤ n)) : a n = b (n : ℤ) := by
    simp only [a, h, ↓reduceIte]
  have ha_zero (n : ℕ) (h : n = 0 ∨ p ≤ n) : a n = 0 := by
    simp only [a, h, ↓reduceIte]
  refine ⟨a, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, fun n h1 hle => ha_eq n (by omega)⟩
  · intro n h1 hle
    have hneg : ¬(n = 0 ∨ p ≤ n) := by omega
    rw [ha_eq n hneg]
    exact hb.1 (n : ℤ)
  · intro n h
    exact ha_zero n h
  · have hneg : ¬((1 : ℕ) = 0 ∨ p ≤ 1) := by omega
    rw [ha_eq 1 hneg]
    have : ((1 : ℕ) : ℤ) = 1 := by simp
    rw [this]
    exact hb.2.2.1
  · intro n h1 hle
    have hnD : ¬(n = 0 ∨ p ≤ n) := by omega
    have hmD : ¬(p - n = 0 ∨ p ≤ p - n) := by omega
    rw [ha_eq n hnD, ha_eq (p - n) hmD]
    have hnp : n ≤ p := by omega
    have hcast : (((p - n : ℕ)) : ℤ) = (p : ℤ) - (n : ℤ) := by
      rw [Nat.cast_sub hnp]
    rw [hcast]
    -- Reduce to b n = b (p - n) via reflection + periodicity
    have hb_per : Function.Periodic b (l + 1 : ℤ) := hb.2.1
    -- Congruence as integers
    have hNatEq : ((((2 * s + 1) % (l + 1) : ℕ)) : ℤ) = (((p % (l + 1) : ℕ)) : ℤ) := by
      rw [hcong]
    rw [Int.natCast_emod, Int.natCast_emod] at hNatEq
    push_cast at hNatEq
    -- hNatEq : (2*s+1) % M = p % M
    have hSub : ((2 * (s : ℤ) + 1 - (p : ℤ)) % (l + 1 : ℤ)) = 0 := by
      rw [Int.sub_emod, hNatEq, sub_self]
      exact Int.zero_emod _
    have hdvd : (l + 1 : ℤ) ∣ (2 * (s : ℤ) + 1 - (p : ℤ)) :=
      Int.dvd_iff_emod_eq_zero.mpr hSub
    obtain ⟨k, hk⟩ := hdvd
    have hrefl := hb.2.2.2.2 ((p : ℤ) - (n : ℤ) - (s : ℤ) - 1)
    have e1 : (s : ℤ) - ((p : ℤ) - (n : ℤ) - (s : ℤ) - 1)
        = 2 * (s : ℤ) + 1 - (p : ℤ) + (n : ℤ) := by
      ring
    have e2 : (s : ℤ) + 1 + ((p : ℤ) - (n : ℤ) - (s : ℤ) - 1) = (p : ℤ) - (n : ℤ) := by
      ring
    rw [e1, e2] at hrefl
    have hperP : Function.Periodic b (k * (l + 1 : ℤ)) := by
      simpa only [Int.cast_id] using (hb_per.int_mul k)
    have hper0 := hperP (n : ℤ)
    have hkM : k * (l + 1 : ℤ) = 2 * (s : ℤ) + 1 - (p : ℤ) := by
      rw [mul_comm]; exact hk.symm
    have e3 : (n : ℤ) + k * (l + 1 : ℤ) = 2 * (s : ℤ) + 1 - (p : ℤ) + (n : ℤ) := by
      rw [hkM]; ring
    rw [e3] at hper0
    exact hper0.symm.trans hrefl
  · intro n h1 hle
    have hnD : ¬(n = 0 ∨ p ≤ n) := by
      have : n ≤ l := by omega
      omega
    have hmD : ¬(l + 1 - n = 0 ∨ p ≤ l + 1 - n) := by
      omega
    rw [ha_eq n hnD, ha_eq (l + 1 - n) hmD]
    have hnlt : n < l + 1 := by omega
    have hcast : (((l + 1 - n : ℕ)) : ℤ) = (l + 1 : ℤ) - (n : ℤ) := by
      rw [Nat.cast_sub (by omega : n ≤ l + 1)]
      push_cast
      ring
    rw [hcast]
    apply hb.2.2.2.1 (n : ℤ)
    have h0 : (0 : ℤ) ≤ (n : ℤ) := Int.natCast_nonneg n
    have hlt : (n : ℤ) < (l + 1 : ℤ) := by exact_mod_cast hnlt
    have heq : Int.emod (n : ℤ) (l + 1 : ℤ) = (n : ℤ) := Int.emod_eq_of_lt h0 hlt
    rw [heq]
    have hne : (n : ℤ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
    exact hne
  · intro n h1 hle
    have hnD : ¬(n = 0 ∨ p ≤ n) := by omega
    have hmD : ¬(l + 1 + n = 0 ∨ p ≤ l + 1 + n) := by omega
    rw [ha_eq n hnD, ha_eq (l + 1 + n) hmD]
    have hcast : (((l + 1 + n : ℕ)) : ℤ) = (n : ℤ) + (l + 1 : ℤ) := by
      push_cast
      ring
    rw [hcast]
    exact (hb.2.1 (n : ℤ)).symm

private theorem step_helper (p l : ℕ) (a : ℕ → ℤ) (ha : IsGobelASequence p l a) :
    ∀ k r, 1 ≤ r → r ≤ l + 1 → r + k * (l + 1) ≤ p - 1 → a r = a (r + k * (l + 1)) := by
  intro k
  induction k with
  | zero =>
    intro r _ _ _
    simp
  | succ k ih =>
    intro r hr1 hrM hbound
    have hsucc : (k + 1) * (l + 1) = k * (l + 1) + (l + 1) := by ring
    rw [hsucc] at hbound
    have h1 : 1 ≤ r + k * (l + 1) := by omega
    have h2 : r + k * (l + 1) ≤ p - l - 2 := by omega
    have hstep := ha.2.2.2.2.2 (r + k * (l + 1)) h1 h2
    have heq : l + 1 + (r + k * (l + 1)) = r + (k * (l + 1) + (l + 1)) := by ring
    rw [heq] at hstep
    have hboundk : r + k * (l + 1) ≤ p - 1 := by omega
    have ih' := ih r hr1 hrM hboundk
    -- hstep : a (r+k*M) = a (r+(k*M+M)), goal : a r = a (r+(k*M+M))
    have hgoal : r + (k + 1) * (l + 1) = r + (k * (l + 1) + (l + 1)) := by
      rw [hsucc]
    rw [hgoal]
    exact ih'.trans hstep

private theorem reduction (p l : ℕ) (a : ℕ → ℤ)
    (step : ∀ k r, 1 ≤ r → r ≤ l + 1 → r + k * (l + 1) ≤ p - 1 → a r = a (r + k * (l + 1)))
    (n : ℕ) (h1 : 1 ≤ n) (hle : n ≤ p - 1) :
    a n = a (if n % (l + 1) = 0 then l + 1 else n % (l + 1)) := by
  have hdiv := Nat.div_add_mod n (l + 1)
  by_cases hr0 : n % (l + 1) = 0
  · simp only [hr0, ↓reduceIte]
    have hq0 : n / (l + 1) ≠ 0 := by
      rintro hq
      have hn0 : n = 0 := by
        rw [← hdiv, hq, hr0]
        simp
      omega
    obtain ⟨q', hq'⟩ := Nat.exists_eq_succ_of_ne_zero hq0
    rw [Nat.succ_eq_add_one] at hq'
    have hdiv2 := hdiv
    rw [hq', hr0] at hdiv2
    simp only [Nat.add_zero] at hdiv2
    have hn : n = (l + 1) + q' * (l + 1) := by
      rw [← hdiv2]; ring
    rw [hn]
    exact (step q' (l + 1) (by omega) (by omega) (hn ▸ hle)).symm
  · simp only [hr0, ↓reduceIte]
    have hr1 : 1 ≤ n % (l + 1) := Nat.pos_of_ne_zero hr0
    have hrM : n % (l + 1) ≤ l + 1 :=
      Nat.le_of_lt (Nat.mod_lt n (by omega : 0 < l + 1))
    have hn : n = n % (l + 1) + (n / (l + 1)) * (l + 1) := by
      have h := hdiv
      rw [mul_comm, add_comm] at h
      exact h.symm
    conv_lhs => rw [hn]
    exact (step (n / (l + 1)) (n % (l + 1)) hr1 hrM (hn ▸ hle)).symm

private theorem symm_all (p l : ℕ) (hp : p.Prime) (hmod : p % 4 = 1)
    (a : ℕ → ℤ) (ha : IsGobelASequence p l a)
    (m : ℕ) (h1 : 1 ≤ m) (hle : m ≤ p - 1) : a m = a (p - m) := by
  have hp2 := hp.two_le
  have h2X : 2 * ((p - 1) / 2) + 1 = p := by omega
  have hsum : m + (p - m) = p := Nat.add_sub_cancel' (by omega : m ≤ p)
  have hpm1 : 1 ≤ p - m := by omega
  have hpmle : p - m ≤ p - 1 := by omega
  by_cases hm : m ≤ (p - 1) / 2
  · exact ha.2.2.2.1 m h1 hm
  · have hpm : p - m ≤ (p - 1) / 2 := by omega
    have h := ha.2.2.2.1 (p - m) hpm1 hpm
    have hback : p - (p - m) = m := by omega
    rw [hback] at h
    exact h.symm

private theorem extendA_mem_pm1_periodic (p l : ℕ) (hp : p.Prime) (hmod : p % 4 = 1)
    (hl : l ≤ p - 3) (a : ℕ → ℤ) (ha : IsGobelASequence p l a) (n : ℤ) :
    (extendA l a n = 1 ∨ extendA l a n = -1) ∧
    (extendA l a (n + (l + 1 : ℤ)) = extendA l a n) := by
  have hp2 := hp.two_le
  have h5 : 5 ≤ p := by omega
  have hlnn : (0 : ℤ) ≤ (l : ℤ) := Int.natCast_nonneg l
  have hMpos : (0 : ℤ) < (l + 1 : ℤ) := by omega
  have hMne : (l + 1 : ℤ) ≠ 0 := ne_of_gt hMpos
  have hl1D : 1 ≤ l + 1 ∧ l + 1 ≤ p - 1 := by omega
  constructor
  · unfold extendA
    simp only
    split
    · exact ha.1 (l + 1) hl1D.1 hl1D.2
    · rename_i hr
      have hrnn : 0 ≤ n % (l + 1 : ℤ) := Int.emod_nonneg n hMne
      have hrlt : n % (l + 1 : ℤ) < (l + 1 : ℤ) := Int.emod_lt_of_pos n hMpos
      have hrpos : 0 < n % (l + 1 : ℤ) := lt_of_le_of_ne hrnn (Ne.symm hr)
      have hcast : (((n % (l + 1 : ℤ)).toNat : ℕ) : ℤ) = n % (l + 1 : ℤ) :=
        Int.toNat_of_nonneg hrnn
      have h1 : 1 ≤ (n % (l + 1 : ℤ)).toNat := by omega
      have hle : (n % (l + 1 : ℤ)).toNat ≤ p - 1 := by
        have hlt : (((n % (l + 1 : ℤ)).toNat : ℕ) : ℤ) < (l + 1 : ℤ) := by
          rw [hcast]; exact hrlt
        have hle2 : (n % (l + 1 : ℤ)).toNat < l + 1 := by exact_mod_cast hlt
        omega
      exact ha.1 _ h1 hle
  · unfold extendA
    simp only
    have hper : (n + (l + 1 : ℤ)) % (l + 1 : ℤ) = n % (l + 1 : ℤ) := by
      have h : n + (l + 1 : ℤ) = n + (l + 1 : ℤ) * 1 := by ring
      rw [h, Int.add_mul_emod_self_left]
    rw [hper]

private theorem extendA_one (p l : ℕ) (hp : p.Prime) (a : ℕ → ℤ) (ha : IsGobelASequence p l a) :
    extendA l a 1 = 1 := by
  have hp2 := hp.two_le
  have hlnn : (0 : ℤ) ≤ (l : ℤ) := Int.natCast_nonneg l
  have hMpos : (0 : ℤ) < (l + 1 : ℤ) := by omega
  unfold extendA
  simp only
  by_cases h1 : (1 : ℤ) % (l + 1 : ℤ) = 0
  · simp only [h1, ↓reduceIte]
    -- M ∣ 1, so M = 1, so l = 0, so a (l+1) = a 1 = 1
    have hdvd : (l + 1 : ℤ) ∣ 1 := Int.dvd_iff_emod_eq_zero.mpr h1
    have hM1 : (l + 1 : ℤ) = 1 := by
      have hle : (l + 1 : ℤ) ≤ 1 := Int.le_of_dvd (by omega : (0 : ℤ) < 1) hdvd
      omega
    have hl0 : l = 0 := by
      have : ((l : ℕ) : ℤ) = 0 := by omega
      exact_mod_cast this
    rw [hl0]
    exact ha.2.2.1
  · simp only [h1, ↓reduceIte]
    have hM1 : (1 : ℤ) < (l + 1 : ℤ) := by
      by_contra hle
      have hle2 : (l + 1 : ℤ) ≤ 1 := by omega
      have hge : (1 : ℤ) ≤ (l + 1 : ℤ) := by omega
      have hMeq : (l + 1 : ℤ) = 1 := by omega
      have : (1 : ℤ) % (l + 1 : ℤ) = 0 := by
        rw [hMeq]
        exact Int.emod_one 1
      exact h1 this
    have heq : (1 : ℤ) % (l + 1 : ℤ) = 1 := Int.emod_eq_of_lt (by omega) hM1
    have hcast : ((((1 : ℤ) % (l + 1 : ℤ)).toNat : ℕ) : ℤ) = 1 := by
      rw [Int.toNat_of_nonneg (Int.emod_nonneg 1 (ne_of_gt hMpos)), heq]
    have htoNat : ((1 : ℤ) % (l + 1 : ℤ)).toNat = 1 := by
      have h1c : (((1 : ℕ)) : ℤ) = 1 := by simp
      rw [← h1c] at hcast
      exact Nat.cast_inj.mp hcast
    rw [htoNat]
    exact ha.2.2.1

private theorem extendA_neg (p l : ℕ) (hp : p.Prime) (hleven : Even l)
    (a : ℕ → ℤ) (ha : IsGobelASequence p l a)
    (n : ℤ) (hn : Int.emod n (l + 1 : ℤ) ≠ 0) :
    extendA l a n = -extendA l a ((l + 1 : ℤ) - n) := by
  have hp2 := hp.two_le
  have hlnn : (0 : ℤ) ≤ (l : ℤ) := Int.natCast_nonneg l
  have hMpos : (0 : ℤ) < (l + 1 : ℤ) := by omega
  have hMne : (l + 1 : ℤ) ≠ 0 := ne_of_gt hMpos
  have hrnn : 0 ≤ n % (l + 1 : ℤ) := Int.emod_nonneg n hMne
  have hrlt : n % (l + 1 : ℤ) < (l + 1 : ℤ) := Int.emod_lt_of_pos n hMpos
  have hrpos : 0 < n % (l + 1 : ℤ) := by
    have hem : n % (l + 1 : ℤ) = Int.emod n (l + 1 : ℤ) := rfl
    omega
  have hres : ((l + 1 : ℤ) - n) % (l + 1 : ℤ) = (l + 1 : ℤ) - n % (l + 1 : ℤ) := by
    have h1 : ((l + 1 : ℤ) - n) % (l + 1 : ℤ)
        = ((l + 1 : ℤ) % (l + 1 : ℤ) - n % (l + 1 : ℤ)) % (l + 1 : ℤ) := by
      rw [Int.sub_emod]
    rw [Int.emod_self] at h1
    have h2 : (0 : ℤ) - n % (l + 1 : ℤ)
        = ((l + 1 : ℤ) - n % (l + 1 : ℤ)) + (-1) * (l + 1 : ℤ) := by ring
    have h3 : ((0 : ℤ) - n % (l + 1 : ℤ)) % (l + 1 : ℤ)
        = ((l + 1 : ℤ) - n % (l + 1 : ℤ)) % (l + 1 : ℤ) := by
      rw [h2, Int.add_mul_emod_self_right]
    rw [h1, h3]
    apply Int.emod_eq_of_lt <;> omega
  have hn0 : n % (l + 1 : ℤ) ≠ 0 := by
    have hem : n % (l + 1 : ℤ) = Int.emod n (l + 1 : ℤ) := rfl
    rw [hem]; exact hn
  have hm0 : ((l + 1 : ℤ) - n) % (l + 1 : ℤ) ≠ 0 := by
    rw [hres]
    omega
  unfold extendA
  simp only [hn0, hm0, ↓reduceIte]
  rw [hres]
  have hcast1 : ((((n % (l + 1 : ℤ)).toNat : ℕ)) : ℤ) = n % (l + 1 : ℤ) :=
    Int.toNat_of_nonneg hrnn
  have hr1 : 1 ≤ (n % (l + 1 : ℤ)).toNat := by omega
  have htoNat : (((l + 1 : ℤ) - n % (l + 1 : ℤ)).toNat) = l + 1 - (n % (l + 1 : ℤ)).toNat := by
    have h1 : ((((((l + 1 : ℤ) - n % (l + 1 : ℤ)).toNat : ℕ))) : ℤ)
        = (l + 1 : ℤ) - n % (l + 1 : ℤ) :=
      Int.toNat_of_nonneg (by omega : (0 : ℤ) ≤ (l + 1 : ℤ) - n % (l + 1 : ℤ))
    have h2 : ((((l + 1 - (n % (l + 1 : ℤ)).toNat : ℕ))) : ℤ)
        = (l + 1 : ℤ) - n % (l + 1 : ℤ) := by
      rw [Nat.cast_sub (by
        have hlt : ((((n % (l + 1 : ℤ)).toNat : ℕ)) : ℤ) < (l + 1 : ℤ) := by
          rw [hcast1]; exact hrlt
        have : (n % (l + 1 : ℤ)).toNat < l + 1 := by exact_mod_cast hlt
        omega : (n % (l + 1 : ℤ)).toNat ≤ l + 1)]
      push_cast
      rw [hcast1]
    have h3 : ((((((l + 1 : ℤ) - n % (l + 1 : ℤ)).toNat : ℕ))) : ℤ)
        = ((((l + 1 - (n % (l + 1 : ℤ)).toNat : ℕ))) : ℤ) := h1.trans h2.symm
    exact Nat.cast_inj.mp h3
  rw [htoNat]
  by_cases hle : (n % (l + 1 : ℤ)).toNat ≤ l / 2
  · exact ha.2.2.2.2.1 _ hr1 hle
  · set r := (n % (l + 1 : ℤ)).toNat with hrdef
    have hm1 : 1 ≤ l + 1 - r := by omega
    have hm2 : l + 1 - r ≤ l / 2 := by
      obtain ⟨k, hk⟩ := hleven
      omega
    have hsym := ha.2.2.2.2.1 (l + 1 - r) hm1 hm2
    have hback : l + 1 - (l + 1 - r) = r := by omega
    rw [hback] at hsym
    rw [hsym, neg_neg]

private theorem extendA_reflect (p l s : ℕ) (hp : p.Prime) (hmod : p % 4 = 1)
    (hl : l ≤ p - 3) (a : ℕ → ℤ)
    (hcong : (2 * s + 1) % (l + 1) = p % (l + 1))
    (red : ∀ n, 1 ≤ n → n ≤ p - 1 → a n = a (if n % (l + 1) = 0 then l + 1 else n % (l + 1)))
    (symm_all : ∀ m, 1 ≤ m → m ≤ p - 1 → a m = a (p - m))
    (t : ℤ) : extendA l a ((s : ℤ) - t) = extendA l a ((s : ℤ) + 1 + t) := by
  have hp2 := hp.two_le
  have h5 : 5 ≤ p := by omega
  have hlnn : (0 : ℤ) ≤ (l : ℤ) := Int.natCast_nonneg l
  have hMpos : (0 : ℤ) < (l + 1 : ℤ) := by omega
  have hMne : (l + 1 : ℤ) ≠ 0 := ne_of_gt hMpos
  have hM_eq : (l + 1 : ℤ) = ((((l + 1 : ℕ))) : ℤ) := by push_cast; ring
  set mY : ℕ := if ((s : ℤ) + 1 + t) % (l + 1 : ℤ) = 0 then l + 1
    else (((s : ℤ) + 1 + t) % (l + 1 : ℤ)).toNat with hmYdef
  set mX : ℕ := if ((s : ℤ) - t) % (l + 1 : ℤ) = 0 then l + 1
    else (((s : ℤ) - t) % (l + 1 : ℤ)).toNat with hmXdef
  have hmY1 : 1 ≤ mY := by
    rw [hmYdef]
    split
    · omega
    · rename_i hy0
      have hrnn : 0 ≤ ((s : ℤ) + 1 + t) % (l + 1 : ℤ) := Int.emod_nonneg ((s : ℤ) + 1 + t) hMne
      have hpos : 0 < ((s : ℤ) + 1 + t) % (l + 1 : ℤ) := lt_of_le_of_ne hrnn (Ne.symm hy0)
      have hcast : ((((((s : ℤ) + 1 + t) % (l + 1 : ℤ)).toNat : ℕ)) : ℤ)
          = ((s : ℤ) + 1 + t) % (l + 1 : ℤ) :=
        Int.toNat_of_nonneg hrnn
      omega
  have hmYM : mY ≤ l + 1 := by
    rw [hmYdef]
    split
    · omega
    · rename_i hy0
      have hrnn : 0 ≤ ((s : ℤ) + 1 + t) % (l + 1 : ℤ) := Int.emod_nonneg ((s : ℤ) + 1 + t) hMne
      have hrlt : ((s : ℤ) + 1 + t) % (l + 1 : ℤ) < (l + 1 : ℤ) :=
        Int.emod_lt_of_pos ((s : ℤ) + 1 + t) hMpos
      have hcast : ((((((s : ℤ) + 1 + t) % (l + 1 : ℤ)).toNat : ℕ)) : ℤ)
          = ((s : ℤ) + 1 + t) % (l + 1 : ℤ) :=
        Int.toNat_of_nonneg hrnn
      have hlt : ((((((s : ℤ) + 1 + t) % (l + 1 : ℤ)).toNat : ℕ)) : ℤ) < (l + 1 : ℤ) := by
        rw [hcast]; exact hrlt
      have : (((s : ℤ) + 1 + t) % (l + 1 : ℤ)).toNat < l + 1 := by exact_mod_cast hlt
      omega
  have hmYD : mY ≤ p - 1 := by omega
  have hYa : extendA l a ((s : ℤ) + 1 + t) = a mY := by
    unfold extendA
    simp only
    rw [hmYdef]
    split <;> rfl
  have hXa : extendA l a ((s : ℤ) - t) = a mX := by
    unfold extendA
    simp only
    rw [hmXdef]
    split <;> rfl
  have hsym := symm_all mY hmY1 hmYD
  have hmY_le : mY ≤ p := by omega
  have hpm1 : 1 ≤ p - mY := by omega
  have hpmle : p - mY ≤ p - 1 := by omega
  have hred := red (p - mY) hpm1 hpmle
  -- hmY_mod
  have hmY_mod : ((mY : ℕ) : ℤ) % (l + 1 : ℤ) = ((s : ℤ) + 1 + t) % (l + 1 : ℤ) := by
    rw [hmYdef]
    split
    · rename_i hy0
      have hcast : ((((l + 1 : ℕ))) : ℤ) = (l + 1 : ℤ) := by push_cast; ring
      rw [hcast, Int.emod_self, hy0]
    · rename_i hy0
      have hrnn : 0 ≤ ((s : ℤ) + 1 + t) % (l + 1 : ℤ) := Int.emod_nonneg ((s : ℤ) + 1 + t) hMne
      have hcast : ((((((s : ℤ) + 1 + t) % (l + 1 : ℤ)).toNat : ℕ)) : ℤ)
          = ((s : ℤ) + 1 + t) % (l + 1 : ℤ) :=
        Int.toNat_of_nonneg hrnn
      rw [hcast, Int.emod_emod]
  -- ZMod equalities
  have hmY_Z : ((((mY : ℕ)) : ℤ) : ZMod (l + 1)) = ((((s : ℤ) + 1 + t) : ℤ) : ZMod (l + 1)) := by
    rw [hM_eq] at hmY_mod
    have hModEq : ((mY : ℕ) : ℤ) ≡ ((s : ℤ) + 1 + t) [ZMOD ((((l + 1 : ℕ))) : ℤ)] := hmY_mod
    exact (ZMod.intCast_eq_intCast_iff _ _ _).mpr hModEq
  have hcong_Z : ((((2 * s + 1 : ℕ))) : ZMod (l + 1)) = (((p : ℕ)) : ZMod (l + 1)) := by
    have hModEq : (2 * s + 1) ≡ p [MOD l + 1] := hcong
    exact (ZMod.natCast_eq_natCast_iff _ _ _).mpr hModEq
  have hZ : ((((p - mY : ℕ))) : ZMod (l + 1)) = ((((s : ℤ) - t) : ℤ) : ZMod (l + 1)) := by
    have hpm : ((((p - mY : ℕ))) : ZMod (l + 1))
        = (((p : ℕ)) : ZMod (l + 1)) - (((mY : ℕ)) : ZMod (l + 1)) := Nat.cast_sub hmY_le
    rw [hpm]
    push_cast at hmY_Z hcong_Z ⊢
    linear_combination -hcong_Z - hmY_Z
  -- Back to emod
  have hIntEq : ((((p - mY : ℕ))) : ℤ) % (l + 1 : ℤ) = ((s : ℤ) - t) % (l + 1 : ℤ) := by
    have hZ' : ((((((p - mY : ℕ))) : ℤ)) : ZMod (l + 1))
        = ((((s : ℤ) - t) : ℤ) : ZMod (l + 1)) := by
      rw [Int.cast_natCast]
      exact hZ
    have hModEq : ((((p - mY : ℕ))) : ℤ) ≡ ((s : ℤ) - t) [ZMOD ((((l + 1 : ℕ))) : ℤ)] :=
      (ZMod.intCast_eq_intCast_iff _ _ _).mp hZ'
    have hEq : ((((p - mY : ℕ))) : ℤ) % ((((l + 1 : ℕ))) : ℤ)
        = ((s : ℤ) - t) % ((((l + 1 : ℕ))) : ℤ) := hModEq
    rw [← hM_eq] at hEq
    exact hEq
  -- Residue equality
  have hResEq : (if (p - mY) % (l + 1) = 0 then l + 1 else (p - mY) % (l + 1)) = mX := by
    have hNat : (((((p - mY) % (l + 1) : ℕ))) : ℤ) = ((((p - mY : ℕ))) : ℤ) % (l + 1 : ℤ) := by
      rw [hM_eq, ← Int.natCast_emod]
    have hEq : (((((p - mY) % (l + 1) : ℕ))) : ℤ) = ((s : ℤ) - t) % (l + 1 : ℤ) := by
      rw [hNat, hIntEq]
    rw [hmXdef]
    by_cases hx0 : ((s : ℤ) - t) % (l + 1 : ℤ) = 0
    · have hN0 : (p - mY) % (l + 1) = 0 := by
        have h0 : (((((p - mY) % (l + 1) : ℕ))) : ℤ) = 0 := by rw [hEq, hx0]
        exact Nat.cast_eq_zero.mp h0
      simp only [hN0, hx0, ↓reduceIte]
    · have hN0 : (p - mY) % (l + 1) ≠ 0 := by
        intro h
        apply hx0
        rw [← hEq, h]
        simp
      simp only [hN0, hx0, ↓reduceIte]
      have hrnn : 0 ≤ ((s : ℤ) - t) % (l + 1 : ℤ) := Int.emod_nonneg ((s : ℤ) - t) hMne
      have hcast : (((((((s : ℤ) - t) % (l + 1 : ℤ)).toNat : ℕ))) : ℤ)
          = ((s : ℤ) - t) % (l + 1 : ℤ) :=
        Int.toNat_of_nonneg hrnn
      have h3 : (((((p - mY) % (l + 1) : ℕ))) : ℤ)
          = (((((((s : ℤ) - t) % (l + 1 : ℤ)).toNat : ℕ))) : ℤ) := by
        rw [hEq, hcast]
      exact Nat.cast_inj.mp h3
  rw [hResEq] at hred
  exact hXa.trans (hred.symm.trans (hsym.symm.trans hYa.symm))

private theorem extendA_agree (p l : ℕ) (a : ℕ → ℤ)
    (red : ∀ n, 1 ≤ n → n ≤ p - 1 → a n = a (if n % (l + 1) = 0 then l + 1 else n % (l + 1)))
    (n : ℕ) (h1 : 1 ≤ n) (hle : n ≤ p - 1) :
    extendA l a (n : ℤ) = a n := by
  have hM_eq : (l + 1 : ℤ) = (((l + 1 : ℕ)) : ℤ) := by push_cast; ring
  have hNat : (((n % (l + 1) : ℕ)) : ℤ) = (n : ℤ) % (l + 1 : ℤ) := by
    rw [hM_eq, ← Int.natCast_emod]
  unfold extendA
  simp only
  by_cases hn0 : n % (l + 1) = 0
  · have hInt0 : (n : ℤ) % (l + 1 : ℤ) = 0 := by
      rw [← hNat, hn0]
      simp
    simp only [hInt0, ↓reduceIte]
    have hred := red n h1 hle
    simp only [hn0, ↓reduceIte] at hred
    exact hred.symm
  · have hInt0 : (n : ℤ) % (l + 1 : ℤ) ≠ 0 := by
      intro h
      apply hn0
      have hEq : (((n % (l + 1) : ℕ)) : ℤ) = 0 := by rw [hNat, h]
      exact Nat.cast_eq_zero.mp hEq
    simp only [hInt0, ↓reduceIte]
    have hrnn : 0 ≤ (n : ℤ) % (l + 1 : ℤ) := by
      have hlnn : (0 : ℤ) ≤ (l : ℤ) := Int.natCast_nonneg l
      have hMpos : (0 : ℤ) < (l + 1 : ℤ) := by omega
      exact Int.emod_nonneg _ (ne_of_gt hMpos)
    have hcast : ((((n : ℤ) % (l + 1 : ℤ)).toNat : ℕ) : ℤ) = (n : ℤ) % (l + 1 : ℤ) :=
      Int.toNat_of_nonneg hrnn
    have hEq : n % (l + 1) = ((n : ℤ) % (l + 1 : ℤ)).toNat := by
      have h3 : (((n % (l + 1) : ℕ)) : ℤ) = ((((n : ℤ) % (l + 1 : ℤ)).toNat : ℕ) : ℤ) := by
        rw [hNat, hcast]
      exact Nat.cast_inj.mp h3
    rw [← hEq]
    have hred := red n h1 hle
    simp only [hn0, ↓reduceIte] at hred
    exact hred.symm

end existsUnique_gobelASequence

/-- **Existence and uniqueness of the sequence $a_{p,l}$.** Let $p$ be a prime with
$p \equiv 1 \pmod 4$ and let $l$ be an even natural number with $l \le p - 3$. Then exactly one
function $a : \mathbb{N} \to \mathbb{Z}$ satisfies the defining conditions of $a_{p,l}$:
$a(n) = \pm 1$ for $1 \le n \le p - 1$, $a(n) = 0$ for $n = 0$ and for $n \ge p$, $a(1) = 1$,
$a(n) = a(p - n)$ for $1 \le n \le (p - 1)/2$, $a(n) = -a(l + 1 - n)$ for $1 \le n \le l/2$, and
$a(n) = a(l + 1 + n)$ for $1 \le n \le p - l - 2$.

Source: Yuh Kobayashi and Shin-ichiro Seki, *A Note
on Non-Integrality of the (k, l)-Göbel Sequences*, Journal of Integer Sequences 29 (2026),
Article 26.3.8, Proposition 17. -/
public theorem existsUnique_gobelASequence
    (p l : ℕ) (hp : p.Prime) (hmod : p % 4 = 1) (hleven : Even l) (hl : l ≤ p - 3) :
    ∃! a : ℕ → ℤ, IsGobelASequence p l a := by
  obtain ⟨hs_le, hcong, hcop⟩ :=
    existsUnique_gobelASequence.s_facts p l hp hmod hl
  obtain ⟨b0, hb0, huniq⟩ :=
    existsUnique_gobelBSequence l (((p - 1) / 2) % (l + 1)) hleven hs_le hcop
  obtain ⟨a0, ha0, ha0b⟩ := existsUnique_gobelASequence.exists_a_of_b p l
    (((p - 1) / 2) % (l + 1)) hp hmod hl hcong b0 hb0
  refine ⟨a0, ha0, fun a ha => ?_⟩
  have step_a := existsUnique_gobelASequence.step_helper p l a ha
  have red_a : ∀ n, 1 ≤ n → n ≤ p - 1 → a n = a (if n % (l + 1) = 0 then l + 1 else n % (l + 1)) :=
    fun n h1 hle => existsUnique_gobelASequence.reduction p l a step_a n h1 hle
  have symm_a : ∀ m, 1 ≤ m → m ≤ p - 1 → a m = a (p - m) :=
    fun m h1 hle => existsUnique_gobelASequence.symm_all p l hp hmod a ha m h1 hle
  have hb1 : IsGobelBSequence l (((p - 1) / 2) % (l + 1))
      (existsUnique_gobelASequence.extendA l a) := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro n
      exact (existsUnique_gobelASequence.extendA_mem_pm1_periodic p l
        hp hmod hl a ha n).1
    · intro n
      exact (existsUnique_gobelASequence.extendA_mem_pm1_periodic p l
        hp hmod hl a ha n).2
    · exact existsUnique_gobelASequence.extendA_one p l hp a ha
    · intro n hn
      exact existsUnique_gobelASequence.extendA_neg p l hp hleven a ha n hn
    · intro t
      exact existsUnique_gobelASequence.extendA_reflect p l (((p - 1) / 2) % (l + 1))
        hp hmod hl a hcong red_a symm_a t
  have heq := huniq _ hb1
  funext n
  by_cases h : n = 0 ∨ p ≤ n
  · have h1 := ha.2.1 n h
    have h0 := ha0.2.1 n h
    rw [h1, h0]
  · have h1 : 1 ≤ n := by omega
    have hle : n ≤ p - 1 := by omega
    have ha_mem := existsUnique_gobelASequence.extendA_agree p l a red_a n h1 hle
    have hcongr := congrFun heq ((n : ℕ) : ℤ)
    exact ha_mem.symm.trans (hcongr.trans (ha0b n h1 hle).symm)

end MetaMathlibExt
