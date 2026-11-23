/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic.Push

@[expose] public section

namespace MetaMathlibExt

/-! # Fibonacci parity-alternating avoidance -/

private def IsGood (n : ℕ) (π : Equiv.Perm (Fin n)) : Prop :=
  (∀ i, (π i).val % 2 = i.val % 2) ∧
  (∀ i j k : Fin n, i.val < j.val → j.val < k.val →
    ¬ ((π j).val < (π k).val ∧ (π k).val < (π i).val)) ∧
  (∀ i j k : Fin n, i.val < j.val → j.val < k.val →
    ¬ ((π k).val < (π i).val ∧ (π i).val < (π j).val))

private instance (n : ℕ) : DecidablePred (IsGood n) := fun π => by unfold IsGood; infer_instance

private theorem last_block {N : ℕ} (π : Equiv.Perm (Fin (N + 1))) (h : IsGood (N + 1) π) :
    ∀ d, d ≤ N - (π (Fin.last N)).val →
      (π ⟨N - d, by omega⟩ : Fin (N+1)).val = (π (Fin.last N)).val + d := by
  obtain ⟨_, h312, h231⟩ := h
  set c := (π (Fin.last N)).val with hc
  have hcN : c ≤ N := Nat.lt_succ_iff.mp (Fin.is_lt _)
  intro d
  induction d using Nat.strong_induction_on with
  | _ d IH =>
    intro hd
    match d with
    | 0 =>
      simp only [Nat.sub_zero, Nat.add_zero]
      have : (⟨N, by omega⟩ : Fin (N+1)) = Fin.last N := by ext; simp
      rw [this]
    | (e+1) =>
      have hsum : c + e + 1 ≤ N := by omega
      set i0 : Fin (N+1) := ⟨N - (e+1), by omega⟩ with hi0
      have hplus : (π ⟨N - e, by omega⟩ : Fin (N+1)).val = c + e := IH e (by omega) (by omega)
      set a : ℕ := (π i0).val with ha
      have hge : c ≤ a := by
        by_contra hlt
        push Not at hlt
        set p : Fin (N+1) := π.symm ⟨c + e + 1, by omega⟩ with hp
        have hpv : (π p).val = c + e + 1 := by rw [hp]; simp
        have hpi : p.val < i0.val := by
          have hne : p ≠ i0 := by intro heq; rw [heq] at hpv; omega
          have hlt2 : p.val < N - e := by
            by_contra hge2
            push Not at hge2
            have hIHp := IH (N - p.val) (by omega) (by omega)
            have hpp : (⟨N - (N - p.val), by omega⟩ : Fin (N+1)) = p := by ext; simp; omega
            rw [hpp] at hIHp
            omega
          have hnev : p.val ≠ i0.val := fun hh => hne (Fin.ext hh)
          have hi0v : i0.val = N - (e+1) := by rw [hi0]
          omega
        have e1 : (π i0).val < (π ⟨N - e, by omega⟩ : Fin (N+1)).val := by rw [hplus, ← ha]; omega
        have e2 : (π ⟨N - e, by omega⟩ : Fin (N+1)).val < (π p).val := by rw [hplus, hpv]; omega
        have hik : i0.val < (⟨N - e, by omega⟩ : Fin (N+1)).val := by
          simp only [hi0, Fin.val_mk]; omega
        exact h312 p i0 ⟨N - e, by omega⟩ hpi hik ⟨e1, e2⟩
      have hge2 : c + e + 1 ≤ a := by
        rcases Nat.lt_or_ge a (c + e + 1) with hlt | hge3
        · exfalso
          set j : ℕ := a - c with hj
          have hjle : j ≤ e := by omega
          have hIHj := IH j (by omega) (by omega)
          have hval : (π ⟨N - j, by omega⟩ : Fin (N+1)).val = a := by rw [hIHj]; omega
          have heq : (⟨N - j, by omega⟩ : Fin (N+1)) = i0 := by
            apply π.injective; apply Fin.ext; rw [← ha]; exact hval
          have hcong : N - j = N - (e+1) := by
            have := congrArg Fin.val heq; simpa [hi0] using this
          omega
        · exact hge3
      have hle : a ≤ c + e + 1 := by
        by_contra hgt
        push Not at hgt
        set q : Fin (N+1) := π.symm ⟨c + e + 1, by omega⟩ with hq
        have hqv : (π q).val = c + e + 1 := by rw [hq]; simp
        have hqi : q.val < i0.val := by
          have hne : q ≠ i0 := by intro heq; rw [heq] at hqv; omega
          have hlt2 : q.val < N - e := by
            by_contra hge2
            push Not at hge2
            have hIHq := IH (N - q.val) (by omega) (by omega)
            have hqq : (⟨N - (N - q.val), by omega⟩ : Fin (N+1)) = q := by ext; simp; omega
            rw [hqq] at hIHq
            omega
          have hnev : q.val ≠ i0.val := fun hh => hne (Fin.ext hh)
          have hi0v : i0.val = N - (e+1) := by rw [hi0]
          omega
        have f1 : (π ⟨N - e, by omega⟩ : Fin (N+1)).val < (π q).val := by rw [hplus, hqv]; omega
        have f2 : (π q).val < (π i0).val := by rw [hqv, ← ha]; omega
        have hik : i0.val < (⟨N - e, by omega⟩ : Fin (N+1)).val := by
          simp only [hi0, Fin.val_mk]; omega
        exact h231 q i0 ⟨N - e, by omega⟩ hqi hik ⟨f1, f2⟩
      change a = c + (e + 1)
      omega

private def buildPerm (m L : ℕ) (ρ : Equiv.Perm (Fin m)) : Equiv.Perm (Fin (m + L)) where
  toFun i := if h : i.val < m then ⟨(ρ ⟨i.val, h⟩).val, by have := (ρ ⟨i.val, h⟩).isLt; omega⟩
             else ⟨2*m + L - 1 - i.val, by have := i.isLt; omega⟩
  invFun i := if h : i.val < m then
      ⟨(ρ.symm ⟨i.val, h⟩).val, by have := (ρ.symm ⟨i.val, h⟩).isLt; omega⟩
              else ⟨2*m + L - 1 - i.val, by have := i.isLt; omega⟩
  left_inv i := by
    by_cases h : i.val < m
    · have hv : (ρ ⟨i.val, h⟩).val < m := (ρ ⟨i.val, h⟩).isLt
      simp only [h, dite_eq_left, hv]
      apply Fin.ext
      simp only [Fin.eta, Equiv.symm_apply_apply]
    · simp only [h, dite_eq_right, not_false_iff]
      have hib : i.val < m + L := i.isLt
      have : ¬ (2*m + L - 1 - i.val < m) := by omega
      simp only [this, dite_eq_right, not_false_iff]
      apply Fin.ext
      simp only
      omega
  right_inv i := by
    by_cases h : i.val < m
    · have hv : (ρ.symm ⟨i.val, h⟩).val < m := (ρ.symm ⟨i.val, h⟩).isLt
      simp only [h, dite_eq_left, hv]
      apply Fin.ext
      simp only [Fin.eta, Equiv.apply_symm_apply]
    · simp only [h, dite_eq_right, not_false_iff]
      have hib : i.val < m + L := i.isLt
      have : ¬ (2*m + L - 1 - i.val < m) := by omega
      simp only [this, dite_eq_right, not_false_iff]
      apply Fin.ext
      simp only
      omega

private lemma buildPerm_lt {m L : ℕ} (ρ : Equiv.Perm (Fin m)) (x : Fin (m + L)) (h : x.val < m) :
    (buildPerm m L ρ x).val = (ρ ⟨x.val, h⟩).val := by
  simp only [buildPerm, Equiv.coe_fn_mk, dite_eq_left h]

private lemma buildPerm_ge {m L : ℕ} (ρ : Equiv.Perm (Fin m)) (x : Fin (m + L)) (h : m ≤ x.val) :
    (buildPerm m L ρ x).val = 2*m + L - 1 - x.val := by
  have hn : ¬ x.val < m := by omega
  simp only [buildPerm, Equiv.coe_fn_mk, dite_eq_right hn]

private theorem buildPerm_good {m L : ℕ} (ρ : Equiv.Perm (Fin m)) (hρ : IsGood m ρ)
    (hL : L % 2 = 1) : IsGood (m + L) (buildPerm m L ρ) := by
  obtain ⟨hpar, h312, h231⟩ := hρ
  refine ⟨?_, ?_, ?_⟩
  · intro i
    by_cases h : i.val < m
    · rw [buildPerm_lt ρ i h]; exact hpar ⟨i.val, h⟩
    · rw [buildPerm_ge ρ i (by omega)]
      have hib : i.val < m + L := i.isLt
      omega
  · intro i j k hij hjk ⟨hjk', hki'⟩
    by_cases hk : k.val < m
    · have hi : i.val < m := by omega
      have hj : j.val < m := by omega
      refine h312 ⟨i.val, hi⟩ ⟨j.val, hj⟩ ⟨k.val, hk⟩ hij hjk ?_
      rw [← buildPerm_lt ρ i hi, ← buildPerm_lt ρ j hj, ← buildPerm_lt ρ k hk]
      exact ⟨hjk', hki'⟩
    · have hkge : m ≤ k.val := by omega
      have hkval : (buildPerm m L ρ k).val = 2*m + L - 1 - k.val := buildPerm_ge ρ k hkge
      have hige : m ≤ i.val := by
        by_contra hlt
        push Not at hlt
        have e1 : (buildPerm m L ρ i).val = (ρ ⟨i.val, hlt⟩).val := buildPerm_lt ρ i hlt
        have e2 := (ρ ⟨i.val, hlt⟩).isLt
        have := k.isLt
        omega
      have hjge : m ≤ j.val := by omega
      have hival : (buildPerm m L ρ i).val = 2*m + L - 1 - i.val := buildPerm_ge ρ i hige
      have hjval : (buildPerm m L ρ j).val = 2*m + L - 1 - j.val := buildPerm_ge ρ j hjge
      have := i.isLt; have := j.isLt; have := k.isLt
      omega
  · intro i j k hij hjk ⟨hki', hij'⟩
    by_cases hk : k.val < m
    · have hi : i.val < m := by omega
      have hj : j.val < m := by omega
      refine h231 ⟨i.val, hi⟩ ⟨j.val, hj⟩ ⟨k.val, hk⟩ hij hjk ?_
      rw [← buildPerm_lt ρ i hi, ← buildPerm_lt ρ j hj, ← buildPerm_lt ρ k hk]
      exact ⟨hki', hij'⟩
    · have hkge : m ≤ k.val := by omega
      have hkval : (buildPerm m L ρ k).val = 2*m + L - 1 - k.val := buildPerm_ge ρ k hkge
      have hige : m ≤ i.val := by
        by_contra hlt
        push Not at hlt
        have e1 : (buildPerm m L ρ i).val = (ρ ⟨i.val, hlt⟩).val := buildPerm_lt ρ i hlt
        have e2 := (ρ ⟨i.val, hlt⟩).isLt
        have := k.isLt
        omega
      have hjge : m ≤ j.val := by omega
      have hival : (buildPerm m L ρ i).val = 2*m + L - 1 - i.val := buildPerm_ge ρ i hige
      have hjval : (buildPerm m L ρ j).val = 2*m + L - 1 - j.val := buildPerm_ge ρ j hjge
      have := i.isLt; have := j.isLt; have := k.isLt
      omega

private lemma block_val {N : ℕ} (π : Equiv.Perm (Fin (N + 1))) (h : IsGood (N + 1) π)
    (i : Fin (N + 1))
    (hi : (π (Fin.last N)).val ≤ i.val) :
    (π i).val = (π (Fin.last N)).val + N - i.val := by
  have hiN : i.val ≤ N := Nat.lt_succ_iff.mp i.isLt
  have hlb := last_block π h (N - i.val) (by omega)
  have hpos : (⟨N - (N - i.val), by omega⟩ : Fin (N+1)) = i := by ext; simp; omega
  rw [hpos] at hlb
  omega

private lemma front_val {N : ℕ} (π : Equiv.Perm (Fin (N + 1))) (h : IsGood (N + 1) π)
    (i : Fin (N + 1))
    (hi : i.val < (π (Fin.last N)).val) : (π i).val < (π (Fin.last N)).val := by
  set c := (π (Fin.last N)).val with hc
  by_contra hge
  push Not at hge
  have hv : (π i).val ≤ N := Nat.lt_succ_iff.mp (π i).isLt
  set v := (π i).val with hv2
  have hjlt : c + N - v < N + 1 := by omega
  have hbj := block_val π h ⟨c + N - v, hjlt⟩ (by simp only; omega)
  have hval : (π ⟨c + N - v, hjlt⟩).val = v := by rw [hbj]; simp only; omega
  have heq : (⟨c + N - v, hjlt⟩ : Fin (N+1)) = i := by
    apply π.injective; apply Fin.ext; rw [hval]
  have := congrArg Fin.val heq
  simp only at this
  omega

private lemma front_symm {N : ℕ} (π : Equiv.Perm (Fin (N + 1))) (h : IsGood (N + 1) π)
    (i : Fin (N + 1))
    (hi : i.val < (π (Fin.last N)).val) : (π.symm i).val < (π (Fin.last N)).val := by
  set c := (π (Fin.last N)).val with hc
  by_contra hge
  push Not at hge
  have hbv := block_val π h (π.symm i) hge
  rw [Equiv.apply_symm_apply] at hbv
  have hb : (π.symm i).val ≤ N := Nat.lt_succ_iff.mp (π.symm i).isLt
  omega


private def frontPerm {N : ℕ} (π : Equiv.Perm (Fin (N + 1))) (h : IsGood (N + 1) π) :
    Equiv.Perm (Fin (π (Fin.last N)).val) where
  toFun i := ⟨(π ⟨i.val, by have := i.isLt; have := (π (Fin.last N)).isLt; omega⟩).val,
              front_val π h ⟨i.val, by have := i.isLt; have := (π (Fin.last N)).isLt; omega⟩ i.isLt⟩
  invFun i := ⟨(π.symm ⟨i.val, by have := i.isLt; have := (π (Fin.last N)).isLt; omega⟩).val,
               front_symm π h
                 ⟨i.val, by have := i.isLt; have := (π (Fin.last N)).isLt; omega⟩ i.isLt⟩
  left_inv i := by apply Fin.ext; simp only [Fin.eta, Equiv.symm_apply_apply]
  right_inv i := by apply Fin.ext; simp only [Fin.eta, Equiv.apply_symm_apply]

private lemma frontPerm_apply {N : ℕ} (π : Equiv.Perm (Fin (N + 1))) (h : IsGood (N + 1) π)
    (i : Fin (π (Fin.last N)).val) (hlt : i.val < N + 1) :
    (frontPerm π h i).val = (π ⟨i.val, hlt⟩).val := rfl

private lemma frontPerm_good {N : ℕ} (π : Equiv.Perm (Fin (N + 1))) (h : IsGood (N + 1) π) :
    IsGood (π (Fin.last N)).val (frontPerm π h) := by
  have hcN : (π (Fin.last N)).val ≤ N := Nat.lt_succ_iff.mp (Fin.is_lt _)
  obtain ⟨hpar, h312, h231⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · intro i
    have hlt : i.val < N + 1 := by have := i.isLt; omega
    rw [frontPerm_apply π ⟨hpar, h312, h231⟩ i hlt]
    exact hpar ⟨i.val, hlt⟩
  · intro i j k hij hjk ⟨hjk', hki'⟩
    have hli : i.val < N + 1 := by have := i.isLt; omega
    have hlj : j.val < N + 1 := by have := j.isLt; omega
    have hlk : k.val < N + 1 := by have := k.isLt; omega
    rw [frontPerm_apply π ⟨hpar, h312, h231⟩ j hlj, frontPerm_apply π ⟨hpar, h312, h231⟩ k hlk]
        at hjk'
    rw [frontPerm_apply π ⟨hpar, h312, h231⟩ k hlk, frontPerm_apply π ⟨hpar, h312, h231⟩ i hli]
        at hki'
    exact h312 ⟨i.val, hli⟩ ⟨j.val, hlj⟩ ⟨k.val, hlk⟩ hij hjk ⟨hjk', hki'⟩
  · intro i j k hij hjk ⟨hki', hij'⟩
    have hli : i.val < N + 1 := by have := i.isLt; omega
    have hlj : j.val < N + 1 := by have := j.isLt; omega
    have hlk : k.val < N + 1 := by have := k.isLt; omega
    rw [frontPerm_apply π ⟨hpar, h312, h231⟩ k hlk, frontPerm_apply π ⟨hpar, h312, h231⟩ i hli]
        at hki'
    rw [frontPerm_apply π ⟨hpar, h312, h231⟩ i hli, frontPerm_apply π ⟨hpar, h312, h231⟩ j hlj]
        at hij'
    exact h231 ⟨i.val, hli⟩ ⟨j.val, hlj⟩ ⟨k.val, hlk⟩ hij hjk ⟨hki', hij'⟩


private def recon {m n : ℕ} (ρ : Equiv.Perm (Fin m)) (L : ℕ) (hn : m + L = n) : Equiv.Perm
    (Fin n) :=
  (finCongr hn).permCongr (buildPerm m L ρ)

private lemma recon_val {m n : ℕ} (ρ : Equiv.Perm (Fin m)) (L : ℕ) (hn : m + L = n) (x : Fin n) :
    (recon ρ L hn x).val = (buildPerm m L ρ ⟨x.val, Nat.lt_of_lt_of_eq x.2 hn.symm⟩).val := by
  simp only [recon, Equiv.permCongr_apply, finCongr_apply, finCongr_symm, Fin.val_cast]
  rfl

private lemma isGood_recon {m n : ℕ} (ρ : Equiv.Perm (Fin m)) (hρ : IsGood m ρ) (L : ℕ)
    (hn : m + L = n)
    (hL : L % 2 = 1) : IsGood n (recon ρ L hn) := by
  subst hn
  simp only [recon, finCongr_refl]
  exact buildPerm_good ρ hρ hL


private lemma recon_lt {m n : ℕ} (ρ : Equiv.Perm (Fin m)) (L : ℕ) (hn : m + L = n) (x : Fin n)
    (hx : x.val < m) : (recon ρ L hn x).val = (ρ ⟨x.val, hx⟩).val := by
  rw [recon_val]
  exact buildPerm_lt ρ ⟨x.val, Nat.lt_of_lt_of_eq x.2 hn.symm⟩ hx

private lemma recon_ge {m n : ℕ} (ρ : Equiv.Perm (Fin m)) (L : ℕ) (hn : m + L = n) (x : Fin n)
    (hx : m ≤ x.val) : (recon ρ L hn x).val = 2*m + L - 1 - x.val := by
  rw [recon_val]
  exact buildPerm_ge ρ ⟨x.val, Nat.lt_of_lt_of_eq x.2 hn.symm⟩ hx

private lemma parity_c {N : ℕ} (π : Equiv.Perm (Fin (N + 1))) (h : IsGood (N + 1) π) :
    (N - (π (Fin.last N)).val) % 2 = 0 := by
  obtain ⟨hpar, _, _⟩ := h
  have hp := hpar (Fin.last N)
  have hlast : (Fin.last N).val = N := Fin.val_last N
  have hcN : (π (Fin.last N)).val ≤ N := Nat.lt_succ_iff.mp (Fin.is_lt _)
  omega

private lemma recon_front {N : ℕ} (π : Equiv.Perm (Fin (N + 1))) (h : IsGood (N + 1) π) :
    π = recon (frontPerm π h) (N + 1 - (π (Fin.last N)).val)
          (by have := Nat.lt_succ_iff.mp (Fin.is_lt (π (Fin.last N))); omega) := by
  apply Equiv.ext
  intro x
  apply Fin.ext
  by_cases hx : x.val < (π (Fin.last N)).val
  · rw [recon_lt _ _ _ x hx, frontPerm_apply π h
      ⟨x.val, by have := x.isLt; omega⟩ (by have := x.isLt; omega)]
  · have hxge : (π (Fin.last N)).val ≤ x.val := by omega
    have hcN : (π (Fin.last N)).val ≤ N := Nat.lt_succ_iff.mp (Fin.is_lt _)
    have hxN : x.val ≤ N := Nat.lt_succ_iff.mp x.isLt
    rw [recon_ge _ _ _ x hxge, block_val π h x hxge]
    omega


private def frontFixed {N : ℕ} (b : Fin (N + 1)) (π : Equiv.Perm (Fin (N + 1)))
    (h : IsGood (N + 1) π)
    (hπ : π (Fin.last N) = b) : Equiv.Perm (Fin b.val) where
  toFun i := ⟨(π ⟨i.val, by have := i.isLt; have := b.isLt; omega⟩).val, by
    have hbv : (π (Fin.last N)).val = b.val := by rw [hπ]
    have hlt := front_val π h ⟨i.val, by have := i.isLt; have := b.isLt; omega⟩
      (by rw [hbv]; exact i.isLt)
    rw [hbv] at hlt; exact hlt⟩
  invFun i := ⟨(π.symm ⟨i.val, by have := i.isLt; have := b.isLt; omega⟩).val, by
    have hbv : (π (Fin.last N)).val = b.val := by rw [hπ]
    have hlt := front_symm π h ⟨i.val, by have := i.isLt; have := b.isLt; omega⟩
      (by rw [hbv]; exact i.isLt)
    rw [hbv] at hlt; exact hlt⟩
  left_inv i := by apply Fin.ext; simp only [Fin.eta, Equiv.symm_apply_apply]
  right_inv i := by apply Fin.ext; simp only [Fin.eta, Equiv.apply_symm_apply]

private lemma frontFixed_apply {N : ℕ} (b : Fin (N + 1)) (π : Equiv.Perm (Fin (N + 1)))
    (h : IsGood (N + 1) π)
    (hπ : π (Fin.last N) = b) (i : Fin b.val) (hlt : i.val < N + 1) :
    (frontFixed b π h hπ i).val = (π ⟨i.val, hlt⟩).val := rfl

private lemma frontFixed_good {N : ℕ} (b : Fin (N + 1)) (π : Equiv.Perm (Fin (N + 1)))
    (h : IsGood (N + 1) π)
    (hπ : π (Fin.last N) = b) : IsGood b.val (frontFixed b π h hπ) := by
  have hbN : b.val ≤ N := Nat.lt_succ_iff.mp b.isLt
  obtain ⟨hpar, h312, h231⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · intro i
    have hlt : i.val < N + 1 := by have := i.isLt; omega
    rw [frontFixed_apply b π ⟨hpar, h312, h231⟩ hπ i hlt]
    exact hpar ⟨i.val, hlt⟩
  · intro i j k hij hjk ⟨hjk', hki'⟩
    have hli : i.val < N + 1 := by have := i.isLt; omega
    have hlj : j.val < N + 1 := by have := j.isLt; omega
    have hlk : k.val < N + 1 := by have := k.isLt; omega
    rw [frontFixed_apply b π ⟨hpar, h312, h231⟩ hπ j hlj, frontFixed_apply b π ⟨hpar, h312, h231⟩ hπ
        k hlk] at hjk'
    rw [frontFixed_apply b π ⟨hpar, h312, h231⟩ hπ k hlk, frontFixed_apply b π ⟨hpar, h312, h231⟩ hπ
        i hli] at hki'
    exact h312 ⟨i.val, hli⟩ ⟨j.val, hlj⟩ ⟨k.val, hlk⟩ hij hjk ⟨hjk', hki'⟩
  · intro i j k hij hjk ⟨hki', hij'⟩
    have hli : i.val < N + 1 := by have := i.isLt; omega
    have hlj : j.val < N + 1 := by have := j.isLt; omega
    have hlk : k.val < N + 1 := by have := k.isLt; omega
    rw [frontFixed_apply b π ⟨hpar, h312, h231⟩ hπ k hlk, frontFixed_apply b π ⟨hpar, h312, h231⟩ hπ
        i hli] at hki'
    rw [frontFixed_apply b π ⟨hpar, h312, h231⟩ hπ i hli, frontFixed_apply b π ⟨hpar, h312, h231⟩ hπ
        j hlj] at hij'
    exact h231 ⟨i.val, hli⟩ ⟨j.val, hlj⟩ ⟨k.val, hlk⟩ hij hjk ⟨hki', hij'⟩

private lemma recon_last {N : ℕ} (b : Fin (N + 1)) (ρ : Equiv.Perm (Fin b.val))
    (hn : b.val + (N + 1 - b.val) = N + 1) :
    recon ρ (N + 1 - b.val) hn (Fin.last N) = b := by
  apply Fin.ext
  have hbN : b.val ≤ N := Nat.lt_succ_iff.mp b.isLt
  rw [recon_ge _ _ _ (Fin.last N) (by rw [Fin.val_last]; omega)]
  rw [Fin.val_last]
  omega


private def fiberEquiv {N : ℕ} (b : Fin (N + 1)) (hb : (N - b.val) % 2 = 0) :
    {π : Equiv.Perm (Fin (N+1)) // IsGood (N+1) π ∧ π (Fin.last N) = b} ≃
      {ρ : Equiv.Perm (Fin b.val) // IsGood b.val ρ} where
  toFun π := ⟨frontFixed b π.1 π.2.1 π.2.2, frontFixed_good b π.1 π.2.1 π.2.2⟩
  invFun ρ := ⟨recon ρ.1 (N + 1 - b.val) (by have := Nat.lt_succ_iff.mp b.isLt; omega),
    ⟨isGood_recon ρ.1 ρ.2 (N + 1 - b.val) (by have := Nat.lt_succ_iff.mp b.isLt; omega)
        (by have := Nat.lt_succ_iff.mp b.isLt; omega),
      recon_last b ρ.1 (by have := Nat.lt_succ_iff.mp b.isLt; omega)⟩⟩
  left_inv π := by
    apply Subtype.ext
    apply Equiv.ext
    intro x
    apply Fin.ext
    have hπ := π.2.2
    have hbN : b.val ≤ N := Nat.lt_succ_iff.mp b.isLt
    by_cases hx : x.val < b.val
    · rw [recon_lt _ _ _ x hx,
        frontFixed_apply b π.1 π.2.1 hπ
            ⟨x.val, by have := x.isLt; omega⟩ (by have := x.isLt; omega)]
    · have hxge : b.val ≤ x.val := by omega
      have hxN : x.val ≤ N := Nat.lt_succ_iff.mp x.isLt
      have hlast : (π.1 (Fin.last N)).val = b.val := by rw [hπ]
      rw [recon_ge _ _ _ x hxge, block_val π.1 π.2.1 x (by rw [hlast]; omega), hlast]
      omega
  right_inv ρ := by
    apply Subtype.ext
    apply Equiv.ext
    intro i
    apply Fin.ext
    have hbN : b.val ≤ N := Nat.lt_succ_iff.mp b.isLt
    rw [frontFixed_apply b _ _ _ i (by have := i.isLt; omega),
        recon_lt _ _ _ ⟨i.val, by have := i.isLt; omega⟩ (by have := i.isLt; exact i.isLt)]


private lemma range_sum {N : ℕ} :
    Fintype.card {π : Equiv.Perm (Fin (N+1)) // IsGood (N+1) π} =
      ∑ b ∈ (Finset.range (N+1)).filter (fun b => (N - b) % 2 = 0),
        Fintype.card {ρ : Equiv.Perm (Fin b) // IsGood b ρ} := by
  classical
  rw [Fintype.card_subtype,
    Finset.card_eq_sum_card_fiberwise
      (f := fun π => (π (Fin.last N)).val) (t := Finset.range (N+1))
      (fun π _ => Finset.mem_range.mpr (π (Fin.last N)).isLt),
    Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro v hv
  rw [Finset.mem_range] at hv
  rw [Finset.filter_filter]
  by_cases hpar : (N - v) % 2 = 0
  · rw [ite_eq_left hpar, ← Fintype.card_subtype
      (fun π => IsGood (N+1) π ∧ (π (Fin.last N)).val = v)]
    apply Fintype.card_congr
    refine (Equiv.subtypeEquivRight ?_).trans (fiberEquiv ⟨v, hv⟩ hpar)
    intro π
    constructor
    · rintro ⟨hg, hval⟩; exact ⟨hg, Fin.ext hval⟩
    · rintro ⟨hg, heq⟩; exact ⟨hg, by rw [heq]⟩
  · rw [ite_eq_right hpar, ← Fintype.card_subtype
      (fun π => IsGood (N+1) π ∧ (π (Fin.last N)).val = v),
      Fintype.card_eq_zero_iff]
    refine ⟨fun π => ?_⟩
    obtain ⟨hg, hval⟩ := π.2
    have hpc := parity_c π.1 hg
    rw [hval] at hpc
    exact hpar hpc


private lemma recurrence (m : ℕ) :
    Fintype.card {π : Equiv.Perm (Fin (m+3)) // IsGood (m+3) π} =
      Fintype.card {σ : Equiv.Perm (Fin (m+2)) // IsGood (m+2) σ} +
      Fintype.card {τ : Equiv.Perm (Fin (m+1)) // IsGood (m+1) τ} := by
  have e1 : Fintype.card {π : Equiv.Perm (Fin (m+3)) // IsGood (m+3) π} =
      ∑ b ∈ (Finset.range (m+3)).filter (fun b => (m + 2 - b) % 2 = 0),
        Fintype.card {ρ : Equiv.Perm (Fin b) // IsGood b ρ} := range_sum (N := m+2)
  have e2 : Fintype.card {τ : Equiv.Perm (Fin (m+1)) // IsGood (m+1) τ} =
      ∑ b ∈ (Finset.range (m+1)).filter (fun b => (m - b) % 2 = 0),
        Fintype.card {ρ : Equiv.Perm (Fin b) // IsGood b ρ} := range_sum (N := m)
  have hset : (Finset.range (m+2)).filter (fun b => (m + 2 - b) % 2 = 0)
      = (Finset.range (m+1)).filter (fun b => (m - b) % 2 = 0) := by
    ext b
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  rw [e1, e2, Finset.range_add_one, Finset.filter_insert,
    ite_eq_left (show (m + 2 - (m + 2)) % 2 = 0 by omega),
    Finset.sum_insert (by simp [Finset.mem_filter, Finset.mem_range]), hset]

private theorem card_isGood_eq_fib : ∀ n, 1 ≤ n →
    Fintype.card {π : Equiv.Perm (Fin n) // IsGood n π} = Nat.fib n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro hn
    match n, hn with
    | 1, _ => decide
    | 2, _ => decide
    | (m+3), _ =>
      rw [recurrence m, IH (m+2) (by omega) (by omega), IH (m+1) (by omega) (by omega)]
      have h : Nat.fib (m+3) = Nat.fib (m+1) + Nat.fib (m+2) := Nat.fib_add_two (n := m+1)
      omega

/-- **Fibonacci count of parity-preserving permutations avoiding $312$ and $231$.** For every
integer $n \ge 1$, the number of permutations $\pi$ of $\{0, 1, \dots, n-1\}$ such that
$\pi(i) \equiv i \pmod 2$ for every $i$ and that avoid the patterns $312$ and $231$ equals the
Fibonacci number $F_n$, where $F_1 = F_2 = 1$. Here $\pi$ contains $312$ if there are
$i < j < k$ with $\pi(j) < \pi(k) < \pi(i)$, and contains $231$ if there are $i < j < k$ with
$\pi(k) < \pi(i) < \pi(j)$.

Equivalently, these are the parity-alternating permutations of $\{1, \dots, n\}$ that start with
an odd entry and avoid $312$ and $231$.

Proves `Wanted` entry `fibonacci_card_parity_alternating_avoiding_312_231`.

Source: Per Alexandersson, Samuel Asefa Fufa, and Frether Getachew Kebede, "Pattern-Avoidance and
Fuss–Catalan Numbers", Journal of Integer Sequences 26 (2023), Article 23.4.2, Proposition lines
1757-1759, <https://cs.uwaterloo.ca/journals/JIS/VOL26/Getachew/get3.tex>.
-/
theorem fibonacci_card_parity_alternating_avoiding_312_231 (n : ℕ) (hn : 0 < n) :
    Fintype.card { π : Equiv.Perm (Fin n) //
        (∀ i, (π i).val % 2 = i.val % 2) ∧
        (∀ i j k : Fin n, i.val < j.val → j.val < k.val →
          ¬ ((π j).val < (π k).val ∧ (π k).val < (π i).val)) ∧
        (∀ i j k : Fin n, i.val < j.val → j.val < k.val →
          ¬ ((π k).val < (π i).val ∧ (π i).val < (π j).val)) } = Nat.fib n := by
  exact card_isGood_eq_fib n hn

end MetaMathlibExt
