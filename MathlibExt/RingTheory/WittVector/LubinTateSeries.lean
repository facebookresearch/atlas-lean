/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_WittVector_existsUnique_mvPowerSeries_coeff_single_eq_and_C_mul_add_
pow_card_eq_subst.lean`
and
`P2M/Sol/S_WittVector_existsUnique_mvPowerSeries_coeff_single_eq_and_C_mul_add_
pow_card_eq_subst.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.RingTheory.MvPowerSeries.Substitution
public import Mathlib.RingTheory.WittVector.DiscreteValuationRing
public import Mathlib.RingTheory.WittVector.Identities

import Mathlib.RingTheory.MvPowerSeries.Expand

@[expose] public section

open MvPowerSeries

universe u v

noncomputable section

namespace LubinTateAux

section CoeffCongr

variable {R : Type*} [CommRing R] {τ : Type*}

private theorem coeff_pow_congr {c c' : MvPowerSeries τ R} {n : ℕ}
    (h : ∀ e : τ →₀ ℕ, e.degree ≤ n → coeff e c = coeff e c') {k : ℕ}
    {d : τ →₀ ℕ} (hd : d.degree ≤ n) :
    coeff d (c ^ k) = coeff d (c' ^ k) := by
  classical
  induction k generalizing d with
  | zero => rfl
  | succ k IH =>
    rw [pow_succ, pow_succ, coeff_mul, coeff_mul]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
    have h1 : p.1.degree ≤ n := by
      refine le_trans ?_ hd
      rw [← hp, map_add]
      exact Nat.le_add_right _ _
    have h2 : p.2.degree ≤ n := by
      refine le_trans ?_ hd
      rw [← hp, map_add]
      exact Nat.le_add_left _ _
    rw [IH h1, h p.2 h2]

private theorem coeff_pow_eq_zero_of_degree_lt {c : MvPowerSeries τ R}
    (hc : c.constantCoeff = 0) {l : ℕ} {d : τ →₀ ℕ} (hd : d.degree < l) :
    coeff d (c ^ l) = 0 := by
  classical
  induction l generalizing d with
  | zero => omega
  | succ l IH =>
    rw [pow_succ, coeff_mul]
    refine Finset.sum_eq_zero fun p hp => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
    by_cases h1 : p.1.degree < l
    · rw [IH h1, zero_mul]
    · have h2 : p.2 = 0 := by
        by_contra h2
        have : 1 ≤ p.2.degree := by
          rcases Nat.eq_zero_or_pos p.2.degree with hz | hpos
          · exact absurd ((Finsupp.degree_eq_zero_iff p.2).mp hz) h2
          · exact hpos
        have hdd : p.1.degree + p.2.degree = d.degree := by
          rw [← hp, map_add]
        omega
      rw [h2, coeff_zero_eq_constantCoeff_apply, hc, mul_zero]

private theorem coeff_finsuppProd_pow_eq_zero_of_degree_lt {σ' : Type*}
    {c : σ' → MvPowerSeries τ R} (hc : ∀ j, (c j).constantCoeff = 0)
    {m : σ' →₀ ℕ} {d : τ →₀ ℕ} (hd : d.degree < m.degree) :
    coeff d (m.prod fun j l => c j ^ l) = 0 := by
  classical
  induction m using Finsupp.induction generalizing d with
  | zero =>
    rw [(Finsupp.degree_eq_zero_iff (0 : σ' →₀ ℕ)).mpr rfl] at hd
    omega
  | single_add j l m hjm hl IH =>
    rw [Finsupp.prod_add_index (fun _ _ => pow_zero _) (fun _ _ _ _ => pow_add _ _ _),
      Finsupp.prod_single_index (h := fun j' l' => c j' ^ l') (pow_zero _), coeff_mul]
    refine Finset.sum_eq_zero fun p hp => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
    have hdd : p.1.degree + p.2.degree = d.degree := by
      rw [← hp, map_add]
    have hsum : (Finsupp.single j l + m).degree = l + m.degree := by
      rw [map_add, Finsupp.degree_single]
    by_cases h1 : p.1.degree < l
    · rw [coeff_pow_eq_zero_of_degree_lt (hc j) h1, zero_mul]
    · have h2 : p.2.degree < m.degree := by omega
      rw [IH h2, mul_zero]




private theorem coeff_mul_congr_right {u c c' : MvPowerSeries τ R} {K r : ℕ}
    (hu : ∀ e : τ →₀ ℕ, e.degree < r → coeff e u = 0)
    (hcc : ∀ e : τ →₀ ℕ, e.degree ≤ K → coeff e c = coeff e c')
    {d : τ →₀ ℕ} (hd : d.degree ≤ K + r) :
    coeff d (u * c) = coeff d (u * c') := by
  classical
  rw [coeff_mul, coeff_mul]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
  have hdd : p.1.degree + p.2.degree = d.degree := by
    rw [← hp, map_add]
  by_cases h1 : p.1.degree < r
  · rw [hu p.1 h1, zero_mul, zero_mul]
  · rw [hcc p.2 (by omega)]

private theorem coeff_pow_sub_congr {c c' : MvPowerSeries τ R} {N : ℕ} (hN : 1 ≤ N)
    (hc : c.constantCoeff = 0) (hc' : c'.constantCoeff = 0)
    (hcc : ∀ e : τ →₀ ℕ, e.degree < N → coeff e c = coeff e c') {l : ℕ}
    {d : τ →₀ ℕ} (hd : d.degree ≤ N + l - 2) :
    coeff d (c ^ l) = coeff d (c' ^ l) := by
  classical
  induction l generalizing d with
  | zero => rw [pow_zero, pow_zero]
  | succ l IH =>
    rcases Nat.eq_zero_or_pos l with hl0 | hlpos
    · subst hl0
      rw [pow_one, pow_one]
      exact hcc d (by omega)
    · have step1 : coeff d (c ^ (l + 1)) = coeff d (c ^ l * c') := by
        rw [pow_succ]
        have hvanish : ∀ e : τ →₀ ℕ, e.degree < l → coeff e (c ^ l) = 0 :=
          fun e he => coeff_pow_eq_zero_of_degree_lt hc he
        exact coeff_mul_congr_right (K := N - 1) (r := l) hvanish
          (fun e he => hcc e (by omega)) (by omega)
      have step2 : coeff d (c ^ l * c') = coeff d (c' ^ l * c') := by
        rw [mul_comm (c ^ l) c', mul_comm (c' ^ l) c']
        have hvanish : ∀ e : τ →₀ ℕ, e.degree < 1 → coeff e c' = 0 := by
          intro e he
          have he0 : e = 0 := by
            rcases Nat.eq_zero_or_pos e.degree with hz | hpos
            · exact (Finsupp.degree_eq_zero_iff e).mp hz
            · omega
          subst he0
          rw [coeff_zero_eq_constantCoeff_apply, hc']
        exact coeff_mul_congr_right (K := N + l - 2) (r := 1) hvanish
          (fun e he => IH he) (by omega)
      rw [step1, step2, ← pow_succ]

private theorem coeff_finsuppProd_pow_sub_congr {σ' : Type*} {c c' : σ' → MvPowerSeries τ R}
    {N : ℕ} (hN : 1 ≤ N)
    (hc : ∀ j, (c j).constantCoeff = 0) (hc' : ∀ j, (c' j).constantCoeff = 0)
    (hcc : ∀ j, ∀ e : τ →₀ ℕ, e.degree < N → coeff e (c j) = coeff e (c' j))
    {m : σ' →₀ ℕ} {d : τ →₀ ℕ} (hd : d.degree ≤ N + m.degree - 2) :
    coeff d (m.prod fun j l => c j ^ l) = coeff d (m.prod fun j l => c' j ^ l) := by
  classical
  induction m using Finsupp.induction generalizing d with
  | zero => rw [Finsupp.prod_zero_index, Finsupp.prod_zero_index]
  | single_add j l m hjm hl IH =>
    have hsum : (Finsupp.single j l + m).degree = l + m.degree := by
      rw [map_add, Finsupp.degree_single]
    rw [hsum] at hd
    rw [Finsupp.prod_add_index (fun _ _ => pow_zero _) (fun _ _ _ _ => pow_add _ _ _),
      Finsupp.prod_add_index (fun _ _ => pow_zero _) (fun _ _ _ _ => pow_add _ _ _),
      Finsupp.prod_single_index (h := fun j' l' => c j' ^ l') (pow_zero _),
      Finsupp.prod_single_index (h := fun j' l' => c' j' ^ l') (pow_zero _)]
    have step1 : coeff d ((c j) ^ l * m.prod fun j' l' => c j' ^ l')
        = coeff d ((c' j) ^ l * m.prod fun j' l' => c j' ^ l') := by
      rw [mul_comm ((c j) ^ l) _, mul_comm ((c' j) ^ l) _]
      have hvanish : ∀ e : τ →₀ ℕ, e.degree < m.degree →
          coeff e (m.prod fun j' l' => c j' ^ l') = 0 :=
        fun e he => coeff_finsuppProd_pow_eq_zero_of_degree_lt hc he
      exact coeff_mul_congr_right (K := N + l - 2) (r := m.degree) hvanish
        (fun e he => coeff_pow_sub_congr hN (hc j) (hc' j) (hcc j) he) (by omega)
    have step2 : coeff d ((c' j) ^ l * m.prod fun j' l' => c j' ^ l')
        = coeff d ((c' j) ^ l * m.prod fun j' l' => c' j' ^ l') := by
      have hvanish : ∀ e : τ →₀ ℕ, e.degree < l → coeff e ((c' j) ^ l) = 0 :=
        fun e he => coeff_pow_eq_zero_of_degree_lt (hc' j) he
      exact coeff_mul_congr_right (K := N + m.degree - 2) (r := l) hvanish
        (fun e he => IH he) (by omega)
    rw [step1, step2]

end CoeffCongr

section LubinTate

variable {p : ℕ} [Fact p.Prime] {k : Type*} [Field k] [Fintype k] [CharP k p]

private theorem two_le_card : 2 ≤ Fintype.card k := Fintype.one_lt_card

private theorem card_ne_zero : Fintype.card k ≠ 0 := by
  have := two_le_card (k := k); omega

private theorem constantCoeff_natCast_p : WittVector.constantCoeff (p : WittVector p k) = 0 := by
  rw [WittVector.constantCoeff_apply, WittVector.coeff_p_zero]

private theorem p_ne_zero' : (p : WittVector p k) ≠ 0 := WittVector.p_nonzero p k

private theorem isUnit_one_sub_pow (r : ℕ) : IsUnit (1 - (p : WittVector p k) ^ (r + 1)) := by
  apply WittVector.isUnit_of_coeff_zero_ne_zero
  rw [← WittVector.constantCoeff_apply, map_sub, map_one, map_pow, constantCoeff_natCast_p,
    zero_pow (Nat.succ_ne_zero r), sub_zero]
  exact one_ne_zero

private theorem one_sub_pow_ne_zero (r : ℕ) : (1 - (p : WittVector p k) ^ (r + 1)) ≠ 0 :=
  (isUnit_one_sub_pow r).ne_zero

private theorem exists_eq_p_mul_of_coeff_zero (x : WittVector p k) (hx : x.coeff 0 = 0) :
    ∃ y : WittVector p k, x = (p : WittVector p k) * y := by
  have h1 : x = WittVector.verschiebung (x.shift 1) := by
    have := WittVector.eq_iterate_verschiebung (x := x) (n := 1) (by
      intro i hi
      have hi0 : i = 0 := by omega
      subst hi0
      exact hx)
    simpa using this
  obtain ⟨y, hy⟩ := (WittVector.frobenius_bijective p k).2 (x.shift 1)
  refine ⟨y, ?_⟩
  rw [h1, ← hy, WittVector.verschiebung_frobenius, mul_comm]

variable (p k)

private def fvec (τ : Type*) : τ → MvPowerSeries τ (WittVector p k) :=
  fun s => C (p : WittVector p k) * X s + X s ^ Fintype.card k

private def Comm {τ : Type*} (φ : MvPowerSeries τ (WittVector p k)) : Prop :=
  C (p : WittVector p k) * φ + φ ^ Fintype.card k = subst (fvec p k τ) φ

private def defect {τ : Type*} (θ : MvPowerSeries τ (WittVector p k)) : MvPowerSeries τ
  (WittVector p k) :=
  C (p : WittVector p k) * θ + θ ^ Fintype.card k - subst (fvec p k τ) θ

variable {p k}

section Family

variable {τ : Type*}

private theorem constantCoeff_fvec (s : τ) : constantCoeff (fvec p k τ s) = 0 := by
  simp only [fvec, map_add, map_mul, constantCoeff_C, constantCoeff_X, mul_zero, map_pow,
    zero_pow (card_ne_zero (k := k)), add_zero]

private theorem hasSubst_fvec [Finite τ] : HasSubst (fvec p k τ) :=
  hasSubst_of_constantCoeff_zero constantCoeff_fvec

private theorem constantCoeff_C_mul_X (s : τ) :
    constantCoeff (C (p : WittVector p k) * (X s : MvPowerSeries τ (WittVector p k))) = 0 := by
  rw [map_mul, constantCoeff_X, mul_zero]

end Family

section Leading

variable {τ : Type*} [Fintype τ] [DecidableEq τ]

private theorem finsuppProd_C_mul_X_pow (m : τ →₀ ℕ) :
    (m.prod fun s e => (C (p : WittVector p k) * (X s : MvPowerSeries τ (WittVector p k))) ^ e)
      = C ((p : WittVector p k) ^ m.degree) * monomial m 1 := by
  have h : (fun s e => (C (p : WittVector p k) * (X s : MvPowerSeries τ (WittVector p k))) ^ e)
      = fun s e => C ((p : WittVector p k) ^ e) * X s ^ e := by
    funext s e
    rw [mul_pow, map_pow]
  rw [h, Finsupp.prod_mul, ← monomial_one_eq, ← map_finsuppProd]
  congr 2
  rw [Finsupp.degree_apply, Finsupp.prod, Finset.prod_pow_eq_pow_sum]

private theorem coeff_finsuppProd_fvec_pow {d m : τ →₀ ℕ} (hdm : d.degree = m.degree) :
    coeff d (m.prod fun s e => (fvec p k τ s) ^ e)
      = if d = m then (p : WittVector p k) ^ m.degree else 0 := by
  have hcc : ∀ s, ∀ e : τ →₀ ℕ, e.degree < 2 →
      coeff e (fvec p k τ s) = coeff e (C (p : WittVector p k) * X s) := by
    intro s e he
    rw [fvec, map_add, add_eq_left, coeff_X_pow, ite_eq_right]
    intro h
    subst h
    rw [Finsupp.degree_single] at he
    have := two_le_card (k := k)
    omega
  have key := coeff_finsuppProd_pow_sub_congr (N := 2) (by norm_num)
    (c := fvec p k τ) (c' := fun s => C (p : WittVector p k) * X s)
    constantCoeff_fvec constantCoeff_C_mul_X hcc (m := m) (d := d) (by omega)
  rw [key, finsuppProd_C_mul_X_pow, coeff_C_mul, coeff_monomial]
  split_ifs <;> simp

private theorem coeff_subst_fvec {θ : MvPowerSeries τ (WittVector p k)} {n : ℕ}
    (hθ : ∀ e : τ →₀ ℕ, e.degree < n → coeff e θ = 0) {d : τ →₀ ℕ} (hd : d.degree ≤ n) :
    coeff d (subst (fvec p k τ) θ) = (p : WittVector p k) ^ d.degree * coeff d θ := by
  rw [coeff_subst hasSubst_fvec, finsum_eq_single _ d]
  · rw [coeff_finsuppProd_fvec_pow rfl, ite_eq_left rfl, smul_eq_mul, mul_comm]
  · intro m hm
    rcases lt_trichotomy m.degree d.degree with hlt | heq | hgt
    · rw [hθ m (by omega), zero_smul]
    · rw [coeff_finsuppProd_fvec_pow heq.symm, ite_eq_right (Ne.symm hm), smul_zero]
    · rw [coeff_finsuppProd_pow_eq_zero_of_degree_lt constantCoeff_fvec hgt,
        smul_zero]

end Leading

section Divisible

variable {τ : Type*}

include p in
private theorem pow_card_eq_subst_X_pow (g : MvPowerSeries τ k) :
    g ^ Fintype.card k = subst (fun s : τ => (X s : MvPowerSeries τ k) ^ Fintype.card k) g := by
  obtain ⟨n, hp, hn⟩ := FiniteField.card k p
  have hp0 : p ≠ 0 := hp.ne_zero
  rw [hn, ← map_iterateFrobenius_expand p hp0 g n, iterateFrobenius_eq_pow,
    FiniteField.frobenius_pow hn, RingHom.one_def, MvPowerSeries.map_id, RingHom.id_apply]
  unfold MvPowerSeries.expand
  rw [substAlgHom_apply]

private theorem map_defect_eq_zero [Finite τ] (θ : MvPowerSeries τ (WittVector p k)) :
    MvPowerSeries.map (WittVector.constantCoeff : WittVector p k →+* k) (defect p k θ) = 0 := by
  have hf : HasSubst (fvec p k τ) := hasSubst_fvec
  rw [defect, map_sub, map_add, map_mul, map_pow, map_C, constantCoeff_natCast_p, map_zero,
    zero_mul, zero_add, map_subst hf, sub_eq_zero]
  have hfam : (fun s => MvPowerSeries.map (WittVector.constantCoeff : WittVector p k →+* k)
      (fvec p k τ s)) = fun s : τ => (X s : MvPowerSeries τ k) ^ Fintype.card k := by
    funext s
    simp only [fvec, map_add, map_mul, map_C, constantCoeff_natCast_p, map_zero, zero_mul,
      zero_add, map_pow, map_X]
  rw [hfam]
  exact pow_card_eq_subst_X_pow _

private theorem exists_coeff_defect_eq_mul [Finite τ] (θ : MvPowerSeries τ (WittVector p k))
    (e : τ →₀ ℕ) : ∃ y : WittVector p k, coeff e (defect p k θ) = (p : WittVector p k) * y := by
  apply exists_eq_p_mul_of_coeff_zero
  rw [← WittVector.constantCoeff_apply, ← MvPowerSeries.coeff_map, map_defect_eq_zero, map_zero]

end Divisible

section Unique

variable {τ : Type*} [Fintype τ] [DecidableEq τ]

private theorem eq_zero_or_single_of_degree_le_one {d : τ →₀ ℕ} (hd : d.degree ≤ 1) :
    d = 0 ∨ ∃ s, d = Finsupp.single s 1 := by
  rcases Nat.lt_or_ge d.degree 1 with h0 | h1
  · left
    exact (Finsupp.degree_eq_zero_iff d).mp (by omega)
  · right
    have hdeg : d.degree = 1 := le_antisymm hd h1
    have hmem : d ∈ {d' : τ →₀ ℕ | d'.degree = 1} := hdeg
    rw [← Finsupp.range_single_one] at hmem
    obtain ⟨s, hs⟩ := hmem
    exact ⟨s, hs.symm⟩

private theorem eq_of_comm {φ ψ : MvPowerSeries τ (WittVector p k)}
    (hφ0 : constantCoeff φ = 0) (hψ0 : constantCoeff ψ = 0)
    (h1 : ∀ s, coeff (Finsupp.single s 1) φ = coeff (Finsupp.single s 1) ψ)
    (hφ : Comm p k φ) (hψ : Comm p k ψ) : φ = ψ := by
  suffices key : ∀ n : ℕ, ∀ d : τ →₀ ℕ, d.degree ≤ n + 1 → coeff d φ = coeff d ψ from
    MvPowerSeries.ext fun d => key d.degree d (Nat.le_succ _)
  intro n
  induction n with
  | zero =>
    intro d hd
    rcases eq_zero_or_single_of_degree_le_one hd with rfl | ⟨s, rfl⟩
    · rw [coeff_zero_eq_constantCoeff_apply, coeff_zero_eq_constantCoeff_apply, hφ0, hψ0]
    · exact h1 s
  | succ n IH =>
    intro d hd
    by_cases hlt : d.degree ≤ n + 1
    · exact IH d hlt
    have hdeg : d.degree = n + 2 := by omega
    have hf : HasSubst (fvec p k τ) := hasSubst_fvec
    have hδ : ∀ e : τ →₀ ℕ, e.degree < n + 2 → coeff e (φ - ψ) = 0 := by
      intro e he
      rw [map_sub, IH e (by omega), sub_self]
    have hpow : coeff d (φ ^ Fintype.card k) = coeff d (ψ ^ Fintype.card k) :=
      coeff_pow_sub_congr (N := n + 2) (by omega) hφ0 hψ0
        (fun e he => IH e (by omega)) (by have := two_le_card (k := k); omega)
    have hsub : coeff d (subst (fvec p k τ) φ) - coeff d (subst (fvec p k τ) ψ)
        = (p : WittVector p k) ^ (n + 2) * coeff d (φ - ψ) := by
      rw [← map_sub, ← subst_sub hf, coeff_subst_fvec hδ (le_of_eq hdeg), hdeg]
    have eφ := congrArg (coeff d) hφ
    have eψ := congrArg (coeff d) hψ
    simp only [map_add, coeff_C_mul] at eφ eψ
    have hc : (p : WittVector p k) * (1 - (p : WittVector p k) ^ (n + 1)) * coeff d (φ - ψ) = 0 :=
  by
      have : (p : WittVector p k) * coeff d (φ - ψ)
          = (p : WittVector p k) ^ (n + 2) * coeff d (φ - ψ) := by
        rw [← hsub, ← eφ, ← eψ, hpow, map_sub]
        ring
      linear_combination this
    rcases mul_eq_zero.mp hc with h | h
    · rcases mul_eq_zero.mp h with h' | h'
      · exact absurd h' p_ne_zero'
      · exact absurd h' (one_sub_pow_ne_zero n)
    · rwa [map_sub, sub_eq_zero] at h

end Unique

section Exists

variable {τ : Type*} [Fintype τ] [DecidableEq τ]

open scoped Classical in
private def pdiv (x : WittVector p k) : WittVector p k :=
  if h : ∃ y : WittVector p k, x = (p : WittVector p k) * y then h.choose else 0

private theorem pdiv_spec {x : WittVector p k} (h : ∃ y : WittVector p k, x = (p : WittVector p k)
  * y) :
    x = (p : WittVector p k) * pdiv x := by
  rw [pdiv, dite_eq_left h]
  exact h.choose_spec

private def corr (θ : MvPowerSeries τ (WittVector p k)) (n : ℕ) : MvPowerSeries τ (WittVector p k)
  :=
  fun d => if d.degree = n + 2 then
    -(((isUnit_one_sub_pow (p := p) (k := k) n).unit⁻¹ : (WittVector p k)ˣ) : WittVector p k)
      * pdiv (coeff d (defect p k θ)) else 0

private theorem coeff_corr (θ : MvPowerSeries τ (WittVector p k)) (n : ℕ) (d : τ →₀ ℕ) :
    coeff d (corr θ n) = if d.degree = n + 2 then
      -(((isUnit_one_sub_pow (p := p) (k := k) n).unit⁻¹ : (WittVector p k)ˣ) : WittVector p k)
        * pdiv (coeff d (defect p k θ)) else 0 := rfl

private theorem coeff_corr_of_ne {θ : MvPowerSeries τ (WittVector p k)} {n : ℕ} {d : τ →₀ ℕ}
    (hd : d.degree ≠ n + 2) : coeff d (corr θ n) = 0 := by
  rw [coeff_corr, ite_eq_right hd]

private def approx (c : τ → WittVector p k) : ℕ → MvPowerSeries τ (WittVector p k)
  | 0 => ∑ s, C (c s) * X s
  | n + 1 => approx c n + corr (approx c n) n

private theorem approx_succ (c : τ → WittVector p k) (n : ℕ) :
    approx c (n + 1) = approx c n + corr (approx c n) n := rfl

private theorem coeff_approx_zero (c : τ → WittVector p k) (d : τ →₀ ℕ) :
    coeff d (approx c 0) = ∑ s, if d = Finsupp.single s 1 then c s else 0 := by
  show coeff d (∑ s, C (c s) * X s) = _
  rw [map_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [coeff_C_mul, coeff_X]
  split_ifs <;> simp

private theorem coeff_approx_zero_of_degree_ne_one (c : τ → WittVector p k) {d : τ →₀ ℕ}
    (hd : d.degree ≠ 1) : coeff d (approx c 0) = 0 := by
  rw [coeff_approx_zero]
  refine Finset.sum_eq_zero fun s _ => ?_
  rw [ite_eq_right]
  rintro rfl
  exact hd (Finsupp.degree_single s 1)

private theorem coeff_single_approx_zero (c : τ → WittVector p k) (t : τ) :
    coeff (Finsupp.single t 1) (approx c 0) = c t := by
  rw [coeff_approx_zero, Finset.sum_eq_single t]
  · rw [ite_eq_left rfl]
  · intro s _ hst
    rw [ite_eq_right]
    intro h
    exact hst (Finsupp.single_left_injective one_ne_zero h).symm
  · intro h
    exact absurd (Finset.mem_univ t) h

private theorem coeff_approx_of_le (c : τ → WittVector p k) {n m : ℕ} (hnm : n ≤ m) {d : τ →₀ ℕ}
    (hd : d.degree ≤ n + 1) : coeff d (approx c m) = coeff d (approx c n) := by
  induction m with
  | zero =>
    have hn0 : n = 0 := by omega
    subst hn0
    rfl
  | succ m IH =>
    rcases Nat.lt_or_ge n (m + 1) with hlt | hge
    · rw [approx_succ, map_add, coeff_corr_of_ne (by omega), add_zero]
      exact IH (by omega)
    · have hn : n = m + 1 := by omega
      subst hn
      rfl

private theorem constantCoeff_approx (c : τ → WittVector p k) (n : ℕ) : constantCoeff (approx c n)
  = 0 := by
  have h0 : ((0 : τ →₀ ℕ)).degree = 0 := (Finsupp.degree_eq_zero_iff (0 : τ →₀ ℕ)).mpr rfl
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_approx_of_le c (Nat.zero_le n) (by omega),
    coeff_approx_zero_of_degree_ne_one c (by omega)]

private theorem coeff_single_approx (c : τ → WittVector p k) (n : ℕ) (t : τ) :
    coeff (Finsupp.single t 1) (approx c n) = c t := by
  rw [coeff_approx_of_le c (Nat.zero_le n) (by rw [Finsupp.degree_single]),
    coeff_single_approx_zero]

private theorem coeff_defect_approx (c : τ → WittVector p k) (n : ℕ) {e : τ →₀ ℕ}
    (he : e.degree ≤ n + 1) : coeff e (defect p k (approx c n)) = 0 := by
  have hf : HasSubst (fvec p k τ) := hasSubst_fvec
  induction n generalizing e with
  | zero =>

    have hlin0 : ∀ e' : τ →₀ ℕ, e'.degree < 1 → coeff e' (approx c 0) = 0 :=
      fun e' he' => coeff_approx_zero_of_degree_ne_one c (by omega)
    rw [defect, map_sub, map_add, coeff_C_mul, coeff_subst_fvec hlin0 he,
      coeff_pow_eq_zero_of_degree_lt (constantCoeff_approx c 0)
        (by have := two_le_card (k := k); omega), add_zero]
    rcases eq_zero_or_single_of_degree_le_one he with rfl | ⟨s, rfl⟩
    · rw [coeff_zero_eq_constantCoeff_apply, constantCoeff_approx, mul_zero, mul_zero, sub_self]
    · rw [Finsupp.degree_single, pow_one, sub_self]
  | succ n IH =>

    set θ := approx c n with hθ
    have hθ0 : constantCoeff θ = 0 := constantCoeff_approx c n
    have hκ : ∀ e' : τ →₀ ℕ, e'.degree < n + 2 → coeff e' (corr θ n) = 0 :=
      fun e' he' => coeff_corr_of_ne (by omega)
    have hκ0 : constantCoeff (corr θ n) = 0 := by
      rw [← coeff_zero_eq_constantCoeff_apply]
      exact hκ 0 (by rw [map_zero]; omega)
    have hθ'0 : constantCoeff (θ + corr θ n) = 0 := by rw [map_add, hθ0, hκ0, add_zero]

    have hpow : coeff e ((θ + corr θ n) ^ Fintype.card k) = coeff e (θ ^ Fintype.card k) :=
      coeff_pow_sub_congr (N := n + 2) (by omega) hθ'0 hθ0
        (fun e' he' => by rw [map_add, hκ e' he', add_zero])
        (by have := two_le_card (k := k); omega)
    have hexp : coeff e (defect p k (θ + corr θ n))
        = coeff e (defect p k θ) + ((p : WittVector p k) * coeff e (corr θ n)
            - coeff e (subst (fvec p k τ) (corr θ n))) := by
      simp only [defect, map_sub, map_add, coeff_C_mul, mul_add, subst_add hf, hpow]
      ring
    rw [approx_succ, hexp]
    rcases Nat.lt_or_ge e.degree (n + 2) with hlt | hge
    · rw [IH (by omega), coeff_subst_fvec hκ (le_of_lt hlt), hκ e hlt, mul_zero, mul_zero,
        sub_self, add_zero]
    · have hedeg : e.degree = n + 2 := by omega
      rw [coeff_subst_fvec hκ (le_of_eq hedeg), hedeg, coeff_corr, ite_eq_left hedeg]
      set u : (WittVector p k)ˣ := (isUnit_one_sub_pow (p := p) (k := k) n).unit with hu
      have hu' : (u : WittVector p k) = 1 - (p : WittVector p k) ^ (n + 1) := rfl
      have hdiv := pdiv_spec (exists_coeff_defect_eq_mul θ e)
      set y := pdiv (coeff e (defect p k θ)) with hy
      rw [hdiv]
      have hinv : (u : WittVector p k) * ((u⁻¹ : (WittVector p k)ˣ) : WittVector p k) = 1 :=
        Units.mul_inv u
      linear_combination (-((p : WittVector p k) * y)) * hinv
        + ((p : WittVector p k) * y * ((u⁻¹ : (WittVector p k)ˣ) : WittVector p k)) * hu'

private def ltSeries (c : τ → WittVector p k) : MvPowerSeries τ (WittVector p k) :=
  fun d => coeff d (approx c d.degree)

private theorem coeff_ltSeries (c : τ → WittVector p k) (d : τ →₀ ℕ) :
    coeff d (ltSeries c) = coeff d (approx c d.degree) := rfl

private theorem coeff_ltSeries_of_le (c : τ → WittVector p k) {n : ℕ} {d : τ →₀ ℕ} (hd : d.degree
  ≤ n + 1) :
    coeff d (ltSeries c) = coeff d (approx c n) := by
  rw [coeff_ltSeries]
  rcases Nat.lt_or_ge d.degree (n + 1) with h | h
  · rcases Nat.eq_zero_or_pos d.degree with h0 | hpos
    · rw [h0]
      exact (coeff_approx_of_le c (Nat.zero_le n) (by omega)).symm
    · rw [coeff_approx_of_le c (show d.degree - 1 ≤ d.degree by omega) (by omega)]
      exact (coeff_approx_of_le c (show d.degree - 1 ≤ n by omega) (by omega)).symm
  · exact coeff_approx_of_le c (by omega) (by omega)

private theorem constantCoeff_ltSeries (c : τ → WittVector p k) :
    constantCoeff (ltSeries c) = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply,
    coeff_ltSeries_of_le c (n := 0) (by simp),
    coeff_zero_eq_constantCoeff_apply, constantCoeff_approx]

private theorem coeff_single_ltSeries (c : τ → WittVector p k) (t : τ) :
    coeff (Finsupp.single t 1) (ltSeries c) = c t := by
  rw [coeff_ltSeries_of_le c (n := 0) (by rw [Finsupp.degree_single]), coeff_single_approx]

private theorem coeff_defect_congr {θ θ' : MvPowerSeries τ (WittVector p k)} {n : ℕ}
    (h : ∀ e : τ →₀ ℕ, e.degree ≤ n → coeff e θ = coeff e θ') {d : τ →₀ ℕ} (hd : d.degree ≤ n) :
    coeff d (defect p k θ) = coeff d (defect p k θ') := by
  have hf : HasSubst (fvec p k τ) := hasSubst_fvec
  have hpow : coeff d (θ ^ Fintype.card k) = coeff d (θ' ^ Fintype.card k) :=
    coeff_pow_congr h hd
  have hsub : coeff d (subst (fvec p k τ) θ) = coeff d (subst (fvec p k τ) θ') := by
    rw [← sub_eq_zero, ← map_sub, ← subst_sub hf, coeff_subst hf,
      finsum_eq_zero_of_forall_eq_zero]
    intro m
    rcases Nat.lt_or_ge d.degree m.degree with hlt | hge
    · rw [coeff_finsuppProd_pow_eq_zero_of_degree_lt constantCoeff_fvec hlt,
        smul_zero]
    · rw [map_sub, h m (by omega), sub_self, zero_smul]
  rw [defect, defect, map_sub, map_sub, map_add, map_add, coeff_C_mul, coeff_C_mul, h d hd, hpow,
    hsub]

private theorem comm_ltSeries (c : τ → WittVector p k) : Comm p k (ltSeries c) := by
  unfold Comm
  rw [← sub_eq_zero]
  change defect p k (ltSeries c) = 0
  refine MvPowerSeries.ext fun d => ?_
  rw [map_zero, coeff_defect_congr (θ' := approx c d.degree) (n := d.degree)
    (fun e he => coeff_ltSeries_of_le c (by omega)) le_rfl]
  exact coeff_defect_approx c d.degree (Nat.le_succ _)

end Exists


end LubinTate

end LubinTateAux

/-- For a finite field `k` of cardinality `q` and characteristic `p`, and
prescribed linear coefficients `c s ∈ W(k)`, there is a unique multivariate
power series `φ` over the Witt vectors `W(k)` with zero constant term and
linear coefficients `c` satisfying `p • φ + φ ^ q = φ(pX + X ^ q)` in the
sense of substitution. This is the Lubin–Tate type fixed-point equation for
the series. -/
public theorem WittVector.existsUnique_mvPowerSeries_coeff_single_eq_and_C_mul_add_pow_card_eq_subst
    (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [Fintype k] [CharP k p]
    (τ : Type v) [Finite τ] (c : τ → WittVector p k) :
    ∃! φ : MvPowerSeries τ (WittVector p k),
      MvPowerSeries.constantCoeff φ = 0 ∧
      (∀ s, MvPowerSeries.coeff (Finsupp.single s 1) φ = c s) ∧
      MvPowerSeries.C (p : WittVector p k) * φ + φ ^ Fintype.card k =
        MvPowerSeries.subst
          (fun s => MvPowerSeries.C (p : WittVector p k) * MvPowerSeries.X s +
            MvPowerSeries.X s ^ Fintype.card k) φ := by
  classical
  haveI : Fintype τ := Fintype.ofFinite τ
  refine ⟨LubinTateAux.ltSeries c, ⟨LubinTateAux.constantCoeff_ltSeries c,
    LubinTateAux.coeff_single_ltSeries c, LubinTateAux.comm_ltSeries c⟩, ?_⟩
  rintro ψ ⟨hψ0, hψ1, hψ⟩
  exact LubinTateAux.eq_of_comm hψ0 (LubinTateAux.constantCoeff_ltSeries c)
    (fun s => by rw [hψ1, LubinTateAux.coeff_single_ltSeries]) hψ
    (LubinTateAux.comm_ltSeries c)

