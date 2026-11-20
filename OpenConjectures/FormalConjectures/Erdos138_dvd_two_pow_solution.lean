/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`FormalConjectures/ErdosProblems/138.lean` (Formal Conjectures):
Copyright 2025 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
-/

import Mathlib
















import FormalConjecturesUtil













open Nat Filter

namespace Erdos138








def monoAP_guarantee_set (r k : ℕ) : Set ℕ :=
  { N | ∀ coloring : Finset.Icc 1 N → Fin r, ContainsMonoAPofLength coloring k}

lemma zero_mem_monoAP_guarantee_set_zero : 0 ∈ monoAP_guarantee_set 2 0 := by
  intro coloring
  refine ⟨0, ∅, ?_, ?_⟩
  · simp
  · simp

lemma one_mem_monoAP_guarantee_set_one : 1 ∈ monoAP_guarantee_set 2 1 := by
  intro coloring
  let x : Finset.Icc 1 1 := ⟨1, by simp⟩
  refine ⟨coloring x, {x}, ?_, ?_⟩
  · simp
  · simp [x]

lemma monoAP_guarantee_set_two_nonempty (k : ℕ) :
    (monoAP_guarantee_set 2 k).Nonempty := by
  rcases k with _ | k
  · exact ⟨0, zero_mem_monoAP_guarantee_set_zero⟩
  · obtain ⟨ι, inst, hι⟩ :=
      Combinatorics.Line.exists_mono_in_high_dimension (Fin (k + 1)) (Fin 2)
    letI : Fintype ι := inst
    let N := Fintype.card ι * k + 1
    refine ⟨N, ?_⟩
    intro coloring
    let encode : (ι → Fin (k + 1)) → ℕ := fun v => 1 + ∑ i, (v i).val
    have encode_mem (v : ι → Fin (k + 1)) : encode v ∈ Finset.Icc 1 N := by
      rw [Finset.mem_Icc]
      constructor
      · simp [encode]
      · have hv : ∀ i, (v i).val ≤ k := fun i => Nat.le_of_lt_succ (v i).isLt
        dsimp [encode, N]
        calc
          1 + ∑ i, (v i).val ≤ 1 + ∑ _i : ι, k :=
            Nat.add_le_add_left (Finset.sum_le_sum fun i _ => hv i) 1
          _ = Fintype.card ι * k + 1 := by
            simp [Nat.mul_comm, Nat.add_comm]
    let C : (ι → Fin (k + 1)) → Fin 2 :=
      fun v => coloring ⟨encode v, encode_mem v⟩
    obtain ⟨line, c, hline⟩ := hι C
    let d := (Finset.univ.filter fun i => line.idxFun i = none).card
    have d_pos : 0 < d := by
      obtain ⟨i, hi⟩ := line.proper
      exact Finset.card_pos.mpr ⟨i, by simp [d, hi]⟩
    have encode_line (x : Fin (k + 1)) :
        encode (line x) = encode (line 0) + x.val * d := by
      classical
      have hp (i : ι) : (line x i).val = (line 0 i).val +
          if line.idxFun i = none then x.val else 0 := by
        cases hopt : line.idxFun i with
        | none => simp [Combinatorics.Line.coe_apply, hopt]
        | some a => simp [Combinatorics.Line.coe_apply, hopt]
      dsimp [encode, d]
      calc
        1 + ∑ i, (line x i).val = 1 + ∑ i, ((line 0 i).val +
            if line.idxFun i = none then x.val else 0) := by simp_rw [hp]
        _ = 1 + ∑ i, (line 0 i).val +
            ∑ i, (if line.idxFun i = none then x.val else 0) := by
          rw [Finset.sum_add_distrib]
          omega
        _ = (1 + ∑ i, (line 0 i).val) + x.val *
            (Finset.univ.filter fun i => line.idxFun i = none).card := by
          simp [Finset.sum_ite, Nat.mul_comm]
    let f : Fin (k + 1) → (Finset.Icc 1 N : Set ℕ) :=
      fun x => ⟨encode (line x), encode_mem (line x)⟩
    refine ⟨c, Set.range f, ?_, ?_⟩
    · rw [Set.IsAPOfLength]
      refine ⟨encode (line 0), d, ?_, ?_⟩
      · let g : Fin (k + 1) → ℕ := fun x => encode (line x)
        have hg : Function.Injective g := by
          intro x y hxy
          have hx := encode_line x
          have hy := encode_line y
          dsimp [g] at hxy
          rw [hx, hy] at hxy
          have hm : x.val * d = y.val * d := Nat.add_left_cancel hxy
          apply Fin.ext
          exact Nat.mul_right_cancel d_pos hm
        have himage : (fun x : (Finset.Icc 1 N : Set ℕ) => (x : ℕ)) '' Set.range f =
            Set.range g := by
          ext z
          constructor
          · rintro ⟨m, ⟨x, rfl⟩, rfl⟩
            exact ⟨x, rfl⟩
          · rintro ⟨x, rfl⟩
            exact ⟨f x, ⟨x, rfl⟩, rfl⟩
        rw [himage]
        calc
          ENat.card (Set.range g) = ENat.card (Fin (k + 1)) :=
            ENat.card_congr (Equiv.ofInjective g hg).symm
          _ = (k + 1 : ℕ) := by
            rw [ENat.card_eq_coe_fintype_card]
            simp
      · ext y
        constructor
        · rintro ⟨m, ⟨x, rfl⟩, rfl⟩
          refine ⟨x.val, ?_, ?_⟩
          · exact_mod_cast x.isLt
          · simpa [f, nsmul_eq_mul] using (encode_line x).symm
        · rintro ⟨j, hj, rfl⟩
          have hj' : j < k + 1 := by exact_mod_cast hj
          let x : Fin (k + 1) := ⟨j, hj'⟩
          refine ⟨f x, ⟨x, rfl⟩, ?_⟩
          change encode (line x) = encode (line 0) + j * d
          simpa [x] using encode_line x
    · rintro m ⟨x, rfl⟩
      exact hline x





noncomputable def monoAPNumber (r k : ℕ) : ℕ := sInf (monoAP_guarantee_set r k)

lemma le_monoAPNumber_of_not_guarantee_before {r k L : ℕ}
    (hne : (monoAP_guarantee_set r k).Nonempty)
    (hbad : ∀ N < L, N ∉ monoAP_guarantee_set r k) :
    L ≤ monoAPNumber r k := by
  rw [monoAPNumber, le_csInf_iff'' hne]
  intro N hN
  by_contra hLN
  exact hbad N (Nat.lt_of_not_ge hLN) hN

lemma le_W_of_bad_colorings {k L : ℕ}
    (hbad : ∀ N < L, ∃ coloring : Finset.Icc 1 N → Fin 2,
      ¬ ContainsMonoAPofLength coloring k) :
    L ≤ monoAPNumber 2 k := by
  apply le_monoAPNumber_of_not_guarantee_before
      (monoAP_guarantee_set_two_nonempty k)
  intro N hNL hN
  obtain ⟨coloring, hc⟩ := hbad N hNL
  exact hc (hN coloring)

lemma le_W_of_bad_coloring {k L : ℕ} (hL : 0 < L)
    (coloring : Finset.Icc 1 (L - 1) → Fin 2)
    (hc : ¬ ContainsMonoAPofLength coloring k) :
    L ≤ monoAPNumber 2 k := by
  apply le_W_of_bad_colorings
  intro N hNL
  have hN : N ≤ L - 1 := by omega
  let e : Finset.Icc 1 N → Finset.Icc 1 (L - 1) := fun x =>
    ⟨x.val, Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp x.property).1,
      (Finset.mem_Icc.mp x.property).2.trans hN⟩⟩
  let coloringN : Finset.Icc 1 N → Fin 2 := fun x => coloring (e x)
  refine ⟨coloringN, ?_⟩
  intro hmono
  apply hc
  obtain ⟨c, ap, hap, hcol⟩ := hmono
  refine ⟨c, e '' ap, ?_, ?_⟩
  · have heq : ((fun x : Finset.Icc 1 (L - 1) => x.1) '' (e '' ap)) =
        ((fun x : Finset.Icc 1 N => x.1) '' ap) := by
      ext z
      constructor
      · rintro ⟨m, ⟨x, hx, rfl⟩, rfl⟩
        exact ⟨x, hx, rfl⟩
      · rintro ⟨x, hx, rfl⟩
        exact ⟨e x, ⟨x, hx, rfl⟩, rfl⟩
    change ((fun x : Finset.Icc 1 (L - 1) => x.1) ''
      (e '' ap)).IsAPOfLength k
    rw [heq]
    exact hap
  · rintro m ⟨x, hx, rfl⟩
    exact hcol x hx

lemma exists_bad_coloring_of_lt_two_mul_sub_one {k N : ℕ} (hk : 1 ≤ k)
    (hN : N < 2 * k - 1) :
    ∃ coloring : Finset.Icc 1 N → Fin 2,
      ¬ ContainsMonoAPofLength coloring k := by
  let coloring : Finset.Icc 1 N → Fin 2 := fun x =>
    if x.val < k then 0 else 1
  refine ⟨coloring, ?_⟩
  rintro ⟨c, ap, hap, hmono⟩
  have himage : ENat.card ((fun x => x.1) '' ap) = k := hap.card
  fin_cases c
  · have hsub : (fun x => x.1) '' ap ⊆ (Finset.Ico 1 k : Set ℕ) := by
      rintro z ⟨m, hm, rfl⟩
      have hc := hmono m hm
      have hlt : m.val < k := by
        by_contra hn
        simp [coloring, Nat.lt_of_not_ge hn] at hc
        exact hn hc
      exact Finset.mem_Ico.mpr ⟨(Finset.mem_Icc.mp m.property).1, hlt⟩
    have hcard := Set.encard_le_encard hsub
    change ENat.card ((fun x => x.1) '' ap) ≤
      ENat.card (Finset.Ico 1 k : Set ℕ) at hcard
    rw [himage, ENat.card_eq_coe_fintype_card] at hcard
    simp at hcard
    have : k ≤ k - 1 := by exact_mod_cast hcard
    omega
  · have hsub : (fun x => x.1) '' ap ⊆ (Finset.Icc k N : Set ℕ) := by
      rintro z ⟨m, hm, rfl⟩
      have hc := hmono m hm
      have hge : k ≤ m.val := by
        by_contra hn
        have hlt : m.val < k := Nat.lt_of_not_ge hn
        simp [coloring, hlt] at hc
      exact Finset.mem_Icc.mpr ⟨hge, (Finset.mem_Icc.mp m.property).2⟩
    have hcard := Set.encard_le_encard hsub
    change ENat.card ((fun x => x.1) '' ap) ≤
      ENat.card (Finset.Icc k N : Set ℕ) at hcard
    rw [himage, ENat.card_eq_coe_fintype_card] at hcard
    simp at hcard
    have hh : k ≤ N + 1 - k := by exact_mod_cast hcard
    omega







noncomputable abbrev W : ℕ → ℕ := monoAPNumber 2

lemma W_mem_monoAP_guarantee_set (k : ℕ) :
    W k ∈ monoAP_guarantee_set 2 k := by
  exact Nat.sInf_mem (monoAP_guarantee_set_two_nonempty k)

lemma two_mul_sub_one_le_W (k : ℕ) (hk : 1 ≤ k) : 2 * k - 1 ≤ W k := by
  apply le_W_of_bad_colorings
  intro N hN
  exact exists_bad_coloring_of_lt_two_mul_sub_one hk hN

lemma le_W_iff_exists_bad_coloring {k L : ℕ} (hL : 0 < L) :
    L ≤ W k ↔ ∃ coloring : Finset.Icc 1 (L - 1) → Fin 2,
      ¬ ContainsMonoAPofLength coloring k := by
  constructor
  · intro hle
    by_contra hn
    push_neg at hn
    have hm : L - 1 ∈ monoAP_guarantee_set 2 k := hn
    have hWle : W k ≤ L - 1 := Nat.sInf_le hm
    omega
  · rintro ⟨coloring, hc⟩
    exact le_W_of_bad_coloring hL coloring hc

lemma W_ge_length (k : ℕ) : k ≤ W k := by
  apply le_monoAPNumber_of_not_guarantee_before
      (monoAP_guarantee_set_two_nonempty k)
  intro N hNk hN
  let coloring : Finset.Icc 1 N → Fin 2 := fun _ => 0
  obtain ⟨c, ap, hap, hmono⟩ := hN coloring
  have hsub : (fun x => x.1) '' ap ⊆ (Finset.Icc 1 N : Set ℕ) := by
    rintro z ⟨m, hm, rfl⟩
    exact m.property
  have hcard := Set.encard_le_encard hsub
  change ENat.card ((fun x => x.1) '' ap) ≤
    ENat.card (Finset.Icc 1 N : Set ℕ) at hcard
  rw [hap.card] at hcard
  have hIcc : ENat.card (Finset.Icc 1 N : Set ℕ) = N := by
    rw [ENat.card_eq_coe_fintype_card]
    simp
  rw [hIcc] at hcard
  have : k ≤ N := by exact_mod_cast hcard
  omega

lemma W_zero : W 0 = 0 := by
  apply Nat.eq_zero_of_le_zero
  exact csInf_le' zero_mem_monoAP_guarantee_set_zero

lemma W_one : W 1 = 1 := by
  apply Nat.le_antisymm
  · exact Nat.sInf_le one_mem_monoAP_guarantee_set_one
  · exact W_ge_length 1

def erdos_138_variants_dvd_two_pow_statement : Prop := atTop.Tendsto (fun k => ((W k : ℚ)/ (2 ^ k))) atTop

lemma tendsto_ratio_of_nat_lower
    (h : ∀ n : ℕ, ∀ᶠ k : ℕ in atTop, n * 2 ^ k ≤ W k) :
    erdos_138_variants_dvd_two_pow_statement := by
  rw [erdos_138_variants_dvd_two_pow_statement, Filter.tendsto_atTop]
  intro b
  obtain ⟨n : ℕ, hn⟩ := exists_nat_ge b
  filter_upwards [h n] with k hk
  calc
    b ≤ (n : ℚ) := hn
    _ ≤ (W k : ℚ) / 2 ^ k := by
      rw [le_div_iff₀ (by positivity : (0 : ℚ) < 2 ^ k)]
      exact_mod_cast hk

lemma tendsto_ratio_iff_nat_lower :
    erdos_138_variants_dvd_two_pow_statement ↔
      ∀ n : ℕ, ∀ᶠ k : ℕ in atTop, n * 2 ^ k ≤ W k := by
  constructor
  · intro h n
    rw [erdos_138_variants_dvd_two_pow_statement, Filter.tendsto_atTop] at h
    filter_upwards [h (n : ℚ)] with k hk
    rw [le_div_iff₀ (by positivity : (0 : ℚ) < 2 ^ k)] at hk
    exact_mod_cast hk
  · exact tendsto_ratio_of_nat_lower

lemma tendsto_ratio_iff_eventually_bad_coloring :
    erdos_138_variants_dvd_two_pow_statement ↔
      ∀ n : ℕ, ∀ᶠ k : ℕ in atTop,
        ∃ coloring : Finset.Icc 1 ((n + 1) * 2 ^ k - 1) → Fin 2,
          ¬ ContainsMonoAPofLength coloring k := by
  rw [tendsto_ratio_iff_nat_lower]
  constructor
  · intro h n
    filter_upwards [h (n + 1)] with k hk
    exact (le_W_iff_exists_bad_coloring (by positivity)).mp hk
  · intro h n
    rcases n with _ | n
    · simp
    · filter_upwards [h n] with k hk
      exact (le_W_iff_exists_bad_coloring (by positivity)).mpr hk

lemma exists_distinct_prime_sum_aux (N : ℕ) :
    ∃ S : Finset ℕ, (∀ p ∈ S, Nat.Prime p) ∧
      (S.sum (fun p => p) = N ∨ S.sum (fun p => p) + 1 = N) := by
  induction N using Nat.strong_induction_on with
  | h N ih =>
    by_cases hN : N < 2
    · have hcases : N = 0 ∨ N = 1 := by omega
      rcases hcases with rfl | rfl
      · exact ⟨∅, by simp⟩
      · exact ⟨∅, by simp⟩
    · have hm : N / 2 ≠ 0 := by omega
      obtain ⟨p, hp, hpgt, hple⟩ := Nat.exists_prime_lt_and_le_two_mul (N / 2) hm
      have hpN : p ≤ N := by omega
      have hrN : N - p < N := by omega
      obtain ⟨S, hSprime, hsum⟩ := ih (N - p) hrN
      have hpnot : p ∉ S := by
        intro hpS
        have hpleSum : p ≤ S.sum (fun q => q) :=
          Finset.single_le_sum (fun q hq => Nat.zero_le q) hpS
        omega
      refine ⟨insert p S, ?_, ?_⟩
      · intro q hq
        rw [Finset.mem_insert] at hq
        rcases hq with rfl | hq
        · exact hp
        · exact hSprime q hq
      · have heq : (insert p S).sum (fun q => q) = p + S.sum (fun q => q) :=
          Finset.sum_insert hpnot
        rw [heq]
        omega

lemma prime_inv_pow_sum_le_half (S : Finset ℕ) (hS : ∀ p ∈ S, Nat.Prime p) :
    (∑ p ∈ S, (1 / 2 : ℝ) ^ p) ≤ 1 / 2 := by
  have h0 : 0 ∉ S := fun h => (hS 0 h).ne_zero rfl
  have h1 : 1 ∉ S := fun h => (hS 1 h).ne_one rfl
  have hle := Summable.sum_le_tsum (insert 0 (insert 1 S))
    (fun i hi => by positivity) summable_geometric_two
  rw [tsum_geometric_two] at hle
  simp [h0, h1] at hle
  have heq : (∑ p ∈ S, (1 / 2 : ℝ) ^ p) =
      ∑ p ∈ S, ((2 : ℝ) ^ p)⁻¹ := by
    apply Finset.sum_congr rfl
    intro p hp
    rw [one_div, inv_pow]
  rw [heq]
  linarith

lemma one_sub_sum_le_prod_one_sub {α : Type*} [DecidableEq α]
    (S : Finset α) (f : α → ℝ) (hf0 : ∀ i ∈ S, 0 ≤ f i)
    (hf1 : ∀ i ∈ S, f i ≤ 1) :
    1 - ∑ i ∈ S, f i ≤ ∏ i ∈ S, (1 - f i) := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    have hi := ih (fun i hi => hf0 i (Finset.mem_insert_of_mem hi))
      (fun i hi => hf1 i (Finset.mem_insert_of_mem hi))
    have hprod0 : 0 ≤ ∏ i ∈ S, (1 - f i) :=
      Finset.prod_nonneg fun i hi =>
        sub_nonneg.mpr (hf1 i (Finset.mem_insert_of_mem hi))
    have hprod1 : ∏ i ∈ S, (1 - f i) ≤ 1 := by
      apply Finset.prod_le_one
      · intro i hi
        exact sub_nonneg.mpr (hf1 i (Finset.mem_insert_of_mem hi))
      · intro i hi
        linarith [hf0 i (Finset.mem_insert_of_mem hi)]
    have hfa0 := hf0 a (Finset.mem_insert_self a S)
    nlinarith

lemma pow_sum_eq_prod_pow (S : Finset ℕ) :
    (2 : ℝ) ^ (S.sum fun p => p) = S.prod fun p => (2 : ℝ) ^ p := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih =>
      simp [Finset.sum_insert ha, Finset.prod_insert ha, pow_add, ih]

lemma pow_sum_le_two_mul_prod_mersenne (S : Finset ℕ)
    (hS : ∀ p ∈ S, Nat.Prime p) :
    2 ^ (S.sum fun p => p) ≤ 2 * (S.prod fun p => 2 ^ p - 1) := by
  have hsum := prime_inv_pow_sum_le_half S hS
  have hprod := one_sub_sum_le_prod_one_sub S (fun p => (1 / 2 : ℝ) ^ p)
    (fun p hp => by positivity)
    (fun p hp => pow_le_one₀ (by norm_num) (by norm_num))
  have hhalf : (1 / 2 : ℝ) ≤ ∏ p ∈ S, (1 - (1 / 2 : ℝ) ^ p) := by
    linarith
  have heq : ((S.prod fun p => 2 ^ p - 1 : ℕ) : ℝ) =
      (2 : ℝ) ^ (S.sum fun p => p) *
        ∏ p ∈ S, (1 - (1 / 2 : ℝ) ^ p) := by
    rw [pow_sum_eq_prod_pow]
    rw [← Finset.prod_mul_distrib]
    push_cast
    apply Finset.prod_congr rfl
    intro p hp
    rw [Nat.cast_sub (one_le_pow₀ (by omega))]
    push_cast
    rw [one_div, inv_pow]
    field_simp
  have hreal : ((2 ^ (S.sum fun p => p) : ℕ) : ℝ) ≤
      2 * ((S.prod fun p => 2 ^ p - 1 : ℕ) : ℝ) := by
    rw [heq]
    push_cast
    have : 0 ≤ (2 : ℝ) ^ (S.sum fun p => p) := by positivity
    nlinarith
  exact_mod_cast hreal

lemma mersenne_coprime_of_distinct_primes {p q : ℕ} (hp : Nat.Prime p)
    (hq : Nat.Prime q) (hpq : p ≠ q) :
    Nat.Coprime (2 ^ p - 1) (2 ^ q - 1) := by
  rw [Nat.coprime_iff_gcd_eq_one, Nat.pow_sub_one_gcd_pow_sub_one]
  have hgcd : p.gcd q = 1 := (Nat.coprime_primes hp hq).mpr hpq
  rw [hgcd]
  norm_num

lemma prod_mersenne_dvd {S : Finset ℕ} (hS : ∀ p ∈ S, Nat.Prime p)
    {d : ℕ} (hd : ∀ p ∈ S, 2 ^ p - 1 ∣ d) :
    (S.prod fun p => 2 ^ p - 1) ∣ d := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih =>
    rw [Finset.prod_insert ha]
    apply Nat.Coprime.mul_dvd_of_dvd_of_dvd
    · exact Nat.Coprime.prod_right fun q hq =>
        mersenne_coprime_of_distinct_primes
          (hS a (Finset.mem_insert_self a S))
          (hS q (Finset.mem_insert_of_mem hq)) (ne_of_mem_of_not_mem hq ha).symm
    · exact hd a (Finset.mem_insert_self a S)
    · exact ih (fun p hp => hS p (Finset.mem_insert_of_mem hp))
        (fun p hp => hd p (Finset.mem_insert_of_mem hp))

abbrev BinaryGaloisField (p : ℕ) := GaloisField 2 p

noncomputable def primitiveBinaryUnit (p : ℕ) : (BinaryGaloisField p)ˣ :=
  Classical.choose (IsCyclic.exists_generator (α := (BinaryGaloisField p)ˣ))

lemma primitiveBinaryUnit_generates (p : ℕ) :
    ∀ x : (BinaryGaloisField p)ˣ,
      x ∈ Subgroup.zpowers (primitiveBinaryUnit p) :=
  Classical.choose_spec (IsCyclic.exists_generator (α := (BinaryGaloisField p)ˣ))

lemma primitiveBinaryUnit_order {p : ℕ} (hp : Nat.Prime p) :
    orderOf (primitiveBinaryUnit p) = 2 ^ p - 1 := by
  rw [orderOf_eq_card_of_forall_mem_zpowers (primitiveBinaryUnit_generates p),
    Nat.card_units]
  congr 1
  exact GaloisField.card 2 p hp.ne_zero

lemma primitiveBinaryUnit_pow_period {p n : ℕ} (hp : Nat.Prime p) :
    (primitiveBinaryUnit p : BinaryGaloisField p) ^ (n + (2 ^ p - 1)) =
      (primitiveBinaryUnit p : BinaryGaloisField p) ^ n := by
  have hu : (primitiveBinaryUnit p) ^ (2 ^ p - 1) = 1 := by
    rw [← primitiveBinaryUnit_order hp]
    exact pow_orderOf_eq_one _
  have hv : (primitiveBinaryUnit p : BinaryGaloisField p) ^ (2 ^ p - 1) = 1 := by
    have hv' := congrArg (fun u : (BinaryGaloisField p)ˣ =>
      (u : BinaryGaloisField p)) hu
    simpa only [Units.val_pow_eq_pow_val, Units.val_one] using hv'
  rw [pow_add, hv]
  simp

lemma primitiveBinaryUnit_pow_ne_one_of_not_dvd {p d : ℕ} (hp : Nat.Prime p)
    (hd : ¬ 2 ^ p - 1 ∣ d) :
    (primitiveBinaryUnit p : BinaryGaloisField p) ^ d ≠ 1 := by
  intro h
  have hu : (primitiveBinaryUnit p) ^ d = 1 := by
    ext
    simpa only [Units.val_pow_eq_pow_val, Units.val_one] using h
  have hh : orderOf (primitiveBinaryUnit p) ∣ d :=
    orderOf_dvd_iff_pow_eq_one.mpr hu
  rw [primitiveBinaryUnit_order hp] at hh
  exact hd hh

lemma minpoly_primitiveBinaryUnit_pow_natDegree {p d : ℕ} (hp : Nat.Prime p)
    (hd : ¬ 2 ^ p - 1 ∣ d) :
    (minpoly (ZMod 2) ((primitiveBinaryUnit p : BinaryGaloisField p) ^ d)).natDegree = p := by
  let β : BinaryGaloisField p := (primitiveBinaryUnit p : BinaryGaloisField p) ^ d
  have hβ1 : β ≠ 1 := by
    dsimp [β]
    exact primitiveBinaryUnit_pow_ne_one_of_not_dvd hp hd
  have hdiv : (minpoly (ZMod 2) β).natDegree ∣ p := by
    have h := minpoly.degree_dvd (IsIntegral.of_finite (ZMod 2) β)
    simpa [GaloisField.finrank 2 hp.ne_zero] using h
  rcases (Nat.dvd_prime hp).mp hdiv with hdeg | hdeg
  · exfalso
    have hrange := minpoly.natDegree_eq_one_iff.mp hdeg
    rcases hrange with ⟨z, hz⟩
    fin_cases z
    · have hzero : β = 0 := by simpa using hz.symm
      have hne : β ≠ 0 := by
        dsimp [β]
        exact pow_ne_zero _ (Units.ne_zero _)
      exact hne hzero
    · apply hβ1
      simpa using hz.symm
  · exact hdeg

lemma polynomial_coeff_finset_sum {R ι : Type*} [CommRing R] [DecidableEq ι]
    (s : Finset ι) (f : ι → Polynomial R) (n : ℕ) :
    (∑ i ∈ s, f i).coeff n = ∑ i ∈ s, (f i).coeff n := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp [ha, ih]

noncomputable def recurrenceOfMonic {R : Type*} [CommRing R]
    (P : Polynomial R) : LinearRecurrence R where
  order := P.natDegree
  coeffs i := -P.coeff i

lemma recurrenceOfMonic_charPoly {R : Type*} [CommRing R] {P : Polynomial R}
    (hP : P.Monic) : (recurrenceOfMonic P).charPoly = P := by
  classical
  apply Polynomial.ext
  intro n
  rw [LinearRecurrence.charPoly]
  simp only [recurrenceOfMonic, Polynomial.coeff_sub, Polynomial.coeff_monomial,
    Polynomial.coeff_X_pow]
  rw [polynomial_coeff_finset_sum]
  simp only [Polynomial.coeff_monomial]
  by_cases hn : n = P.natDegree
  · subst n
    have hz : (∑ i : Fin P.natDegree,
        if (i : ℕ) = P.natDegree then -P.coeff i else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      simp [Nat.ne_of_lt i.isLt]
    rw [hz]
    simp [hP.coeff_natDegree]
  · by_cases hlt : n < P.natDegree
    · have hs : (∑ i : Fin P.natDegree,
          if (i : ℕ) = n then -P.coeff i else 0) = -P.coeff n := by
        rw [Finset.sum_eq_single ⟨n, hlt⟩]
        · simp
        · intro b hb hne
          have hv : (b : ℕ) ≠ n := by
            intro he
            exact hne (Fin.ext he)
          simp [hv]
        · simp
      rw [hs]
      simp [hn, Ne.symm hn]
    · have hgt : P.natDegree < n := by omega
      have hc : P.coeff n = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt hgt
      have hz : (∑ i : Fin P.natDegree,
          if (i : ℕ) = n then -P.coeff i else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro i hi
        have hv : (i : ℕ) ≠ n := by omega
        simp [hv]
      rw [hz, hc]
      simp [hn, Ne.symm hn]

noncomputable def recurrenceMap {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (E : LinearRecurrence R) : LinearRecurrence S where
  order := E.order
  coeffs i := f (E.coeffs i)

lemma recurrenceMap_charPoly {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (E : LinearRecurrence R) :
    (recurrenceMap f E).charPoly = E.charPoly.map f := by
  rw [LinearRecurrence.charPoly, LinearRecurrence.charPoly]
  simp [recurrenceMap, Polynomial.map_sub, Polynomial.map_sum]

lemma linearMap_solution {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] (E : LinearRecurrence R) (u : ℕ → S)
    (h : (recurrenceMap (algebraMap R S) E).IsSolution u) (L : S →ₗ[R] R) :
    E.IsSolution (fun n => L (u n)) := by
  intro n
  have hh := congrArg L (h n)
  rw [map_sum] at hh
  simpa [recurrenceMap, ← Algebra.smul_def] using hh

lemma trace_mul_geom_solution {K F : Type*} [Field K] [Field F] [Algebra K F]
    [FiniteDimensional K F] (P : Polynomial K) (hP : P.Monic)
    (β c : F) (hβ : (P.map (algebraMap K F)).IsRoot β) :
    (recurrenceOfMonic P).IsSolution
      (fun n => (Algebra.trace K F) (c * β ^ n)) := by
  let E := recurrenceOfMonic P
  let EF := recurrenceMap (algebraMap K F) E
  have hchar : EF.charPoly = P.map (algebraMap K F) := by
    rw [recurrenceMap_charPoly, recurrenceOfMonic_charPoly hP]
  have hgeom : EF.IsSolution (fun n => β ^ n) := by
    rw [LinearRecurrence.geom_sol_iff_root_charPoly, hchar]
    exact hβ
  have hmul : EF.IsSolution (fun n => c * β ^ n) := by
    intro n
    have hh := congrArg (fun x : F => c * x) (hgeom n)
    change c * β ^ (n + EF.order) =
      c * (∑ i, EF.coeffs i * β ^ (n + (i : ℕ))) at hh
    rw [Finset.mul_sum] at hh
    simpa [mul_assoc, mul_left_comm, mul_comm] using hh
  exact linearMap_solution E (fun n => c * β ^ n) hmul (Algebra.trace K F)

noncomputable def combinedMinpoly (S : Finset ℕ) (d : ℕ) : Polynomial (ZMod 2) :=
  ∏ p ∈ S, minpoly (ZMod 2)
    ((primitiveBinaryUnit p : BinaryGaloisField p) ^ d)

lemma combinedMinpoly_monic (S : Finset ℕ) (d : ℕ) :
    (combinedMinpoly S d).Monic := by
  classical
  apply Polynomial.monic_prod_of_monic
  intro p hp
  exact minpoly.monic (IsIntegral.of_finite (ZMod 2)
    ((primitiveBinaryUnit p : BinaryGaloisField p) ^ d))

lemma combinedMinpoly_natDegree_le (S : Finset ℕ)
    (hS : ∀ p ∈ S, Nat.Prime p) (d : ℕ) :
    (combinedMinpoly S d).natDegree ≤ ∑ p ∈ S, p := by
  classical
  rw [combinedMinpoly, Polynomial.natDegree_prod]
  · apply Finset.sum_le_sum
    intro p hp
    simpa [GaloisField.finrank 2 (hS p hp).ne_zero] using
      (minpoly.natDegree_le (K := ZMod 2)
        ((primitiveBinaryUnit p : BinaryGaloisField p) ^ d))
  · intro p hp
    exact minpoly.ne_zero (IsIntegral.of_finite (ZMod 2)
      ((primitiveBinaryUnit p : BinaryGaloisField p) ^ d))

lemma combinedMinpoly_isRoot (S : Finset ℕ) (d : ℕ) {p : ℕ} (hp : p ∈ S) :
    ((combinedMinpoly S d).map
      (algebraMap (ZMod 2) (BinaryGaloisField p))).IsRoot
      ((primitiveBinaryUnit p : BinaryGaloisField p) ^ d) := by
  classical
  rw [Polynomial.IsRoot, Polynomial.eval_map_algebraMap]
  change Polynomial.aeval ((primitiveBinaryUnit p : BinaryGaloisField p) ^ d)
    (∏ q ∈ S, minpoly (ZMod 2)
      ((primitiveBinaryUnit q : BinaryGaloisField q) ^ d)) = 0
  rw [map_prod]
  apply Finset.prod_eq_zero hp
  exact minpoly.aeval (ZMod 2)
    ((primitiveBinaryUnit p : BinaryGaloisField p) ^ d)

noncomputable def combinedDifference (S : Finset ℕ) (a d i : ℕ) : ZMod 2 :=
  ∑ p ∈ S, (Algebra.trace (ZMod 2) (BinaryGaloisField p))
    (((primitiveBinaryUnit p : BinaryGaloisField p) ^ a *
      ((primitiveBinaryUnit p : BinaryGaloisField p) ^ d - 1)) *
      ((primitiveBinaryUnit p : BinaryGaloisField p) ^ d) ^ i)

lemma combinedDifference_solution (S : Finset ℕ) (a d : ℕ) :
    (recurrenceOfMonic (combinedMinpoly S d)).IsSolution
      (combinedDifference S a d) := by
  classical
  let E := recurrenceOfMonic (combinedMinpoly S d)
  let u : ℕ → ZMod 2 := ∑ p ∈ S, fun i =>
      (Algebra.trace (ZMod 2) (BinaryGaloisField p))
        (((primitiveBinaryUnit p : BinaryGaloisField p) ^ a *
          ((primitiveBinaryUnit p : BinaryGaloisField p) ^ d - 1)) *
          ((primitiveBinaryUnit p : BinaryGaloisField p) ^ d) ^ i)
  have hu : E.IsSolution u := by
    change u ∈ E.solSpace
    dsimp [u]
    apply Submodule.sum_mem
    intro p hp
    exact trace_mul_geom_solution (combinedMinpoly S d)
      (combinedMinpoly_monic S d) _ _ (combinedMinpoly_isRoot S d hp)
  have heq : combinedDifference S a d = u := by
    funext i
    simp only [combinedDifference, u, Finset.sum_apply]
  rw [heq]
  exact hu

lemma solution_eq_zero_of_initial {R : Type*} [CommSemiring R]
    (E : LinearRecurrence R) (u : ℕ → R) (hu : E.IsSolution u)
    (hzero : ∀ i < E.order, u i = 0) : u = 0 := by
  apply (E.sol_eq_of_eq_init u 0 hu (show E.IsSolution (0 : ℕ → R) from E.solSpace.zero_mem)).mpr
  intro i hi
  have hil : i < E.order := by simpa using hi
  simpa using hzero i hil

noncomputable def binaryMSequence (p : ℕ) (n : ℕ) : ZMod 2 :=
  (Algebra.trace (ZMod 2) (BinaryGaloisField p))
    ((primitiveBinaryUnit p : BinaryGaloisField p) ^ n)

noncomputable def combinedZSequence (S : Finset ℕ) (n : ℕ) : ZMod 2 :=
  ∑ p ∈ S, binaryMSequence p n

lemma combinedZSequence_sub (S : Finset ℕ) (a d i : ℕ) :
    combinedZSequence S (a + (i + 1) * d) -
      combinedZSequence S (a + i * d) = combinedDifference S a d i := by
  classical
  simp only [combinedZSequence, combinedDifference, binaryMSequence,
    ← Finset.sum_sub_distrib, map_sub]
  apply Finset.sum_congr rfl
  intro p hp
  rw [← map_sub]
  apply congrArg (Algebra.trace (ZMod 2) (BinaryGaloisField p))
  rw [pow_add, pow_add, add_mul, one_mul, pow_add, pow_mul]
  ring

noncomputable def combinedMSequence (S : Finset ℕ) (n : ℕ) : Fin 2 :=
  (ZMod.finEquiv 2).symm (∑ p ∈ S, binaryMSequence p n)

lemma combinedMSequence_eq_iff (S : Finset ℕ) (m n : ℕ) :
    combinedMSequence S m = combinedMSequence S n ↔
      combinedZSequence S m = combinedZSequence S n := by
  exact (ZMod.finEquiv 2).symm.injective.eq_iff

noncomputable def componentDifference (p a d i : ℕ) : ZMod 2 :=
  (Algebra.trace (ZMod 2) (BinaryGaloisField p))
    (((primitiveBinaryUnit p : BinaryGaloisField p) ^ a *
      ((primitiveBinaryUnit p : BinaryGaloisField p) ^ d - 1)) *
      ((primitiveBinaryUnit p : BinaryGaloisField p) ^ d) ^ i)

lemma combinedDifference_eq_sum (S : Finset ℕ) (a d i : ℕ) :
    combinedDifference S a d i = ∑ p ∈ S, componentDifference p a d i := by
  rfl

lemma primitiveBinaryUnit_pow_eq_one_of_dvd {p m : ℕ} (hp : Nat.Prime p)
    (hm : 2 ^ p - 1 ∣ m) :
    (primitiveBinaryUnit p : BinaryGaloisField p) ^ m = 1 := by
  obtain ⟨t, rfl⟩ := hm
  rw [pow_mul]
  have hu : (primitiveBinaryUnit p) ^ (2 ^ p - 1) = 1 := by
    rw [← primitiveBinaryUnit_order hp]
    exact pow_orderOf_eq_one _
  have hv := congrArg (fun u : (BinaryGaloisField p)ˣ =>
    (u : BinaryGaloisField p)) hu
  simp only [Units.val_pow_eq_pow_val, Units.val_one] at hv
  rw [hv, one_pow]

lemma componentDifference_add_period {p a d i T : ℕ} (hp : Nat.Prime p)
    (hT : 2 ^ p - 1 ∣ T) :
    componentDifference p a d (i + T) = componentDifference p a d i := by
  simp only [componentDifference, pow_add]
  have hone : ((primitiveBinaryUnit p : BinaryGaloisField p) ^ d) ^ T = 1 := by
    rw [← pow_mul]
    exact primitiveBinaryUnit_pow_eq_one_of_dvd hp (dvd_mul_of_dvd_right hT d)
  rw [hone]
  simp

lemma exists_active_prime {S : Finset ℕ} (hS : ∀ p ∈ S, Nat.Prime p)
    {d : ℕ} (hdQ : ¬ (S.prod fun p => 2 ^ p - 1) ∣ d) :
    ∃ p ∈ S, ¬ 2 ^ p - 1 ∣ d := by
  by_contra h
  push_neg at h
  exact hdQ (prod_mersenne_dvd hS h)

lemma mersenne_coprime_prod_erase {S : Finset ℕ}
    (hS : ∀ p ∈ S, Nat.Prime p) {p : ℕ} (hpS : p ∈ S) :
    Nat.Coprime (2 ^ p - 1) ((S.erase p).prod fun q => 2 ^ q - 1) := by
  apply Nat.Coprime.prod_right
  intro q hq
  exact mersenne_coprime_of_distinct_primes (hS p hpS)
    (hS q (Finset.mem_of_mem_erase hq)) (Finset.ne_of_mem_erase hq).symm

lemma componentDifference_nonzero_somewhere {p a d T : ℕ} (hp : Nat.Prime p)
    (hd : ¬ 2 ^ p - 1 ∣ d) (hT : Nat.Coprime (2 ^ p - 1) T) :
    ∃ i : ℕ, componentDifference p a d (i + T) ≠
      componentDifference p a d i := by
  let α : BinaryGaloisField p := primitiveBinaryUnit p
  let β : BinaryGaloisField p := α ^ d
  have hβ : β ≠ 1 := by
    dsimp [β, α]
    exact primitiveBinaryUnit_pow_ne_one_of_not_dvd hp hd
  have hdT : ¬ 2 ^ p - 1 ∣ d * T := by
    intro hh
    exact hd (hT.dvd_of_dvd_mul_right hh)
  have hβT : β ^ T ≠ 1 := by
    dsimp [β, α]
    rw [← pow_mul]
    exact primitiveBinaryUnit_pow_ne_one_of_not_dvd hp hdT
  let c : BinaryGaloisField p := α ^ a * (β - 1) * (β ^ T - 1)
  have hc : c ≠ 0 := by
    dsimp [c]
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ (Units.ne_zero _))
      (sub_ne_zero.mpr hβ)) (sub_ne_zero.mpr hβT)
  obtain ⟨b, hb⟩ : ∃ b : BinaryGaloisField p,
      (Algebra.trace (ZMod 2) (BinaryGaloisField p)) (c * b) ≠ 0 := by
    by_contra hn
    push_neg at hn
    apply hc
    apply (traceForm_nondegenerate (ZMod 2) (BinaryGaloisField p) c)
    intro b
    simpa only [Algebra.traceForm_apply] using hn b
  have hlin : LinearIndependent (ZMod 2)
      (fun i : Fin p => β ^ (i : ℕ)) := by
    have hh := linearIndependent_pow (K := ZMod 2) β
    rw [minpoly_primitiveBinaryUnit_pow_natDegree hp hd] at hh
    exact hh
  letI : Nonempty (Fin p) := Fin.pos_iff_nonempty.mp hp.pos
  let B : Module.Basis (Fin p) (ZMod 2) (BinaryGaloisField p) :=
    basisOfLinearIndependentOfCardEqFinrank hlin (by
      simp [GaloisField.finrank 2 hp.ne_zero])
  have hbexp := B.sum_repr b
  by_contra hall
  push_neg at hall
  have hzero (i : Fin p) :
      (Algebra.trace (ZMod 2) (BinaryGaloisField p)) (c * β ^ (i : ℕ)) = 0 := by
    have heq : componentDifference p a d ((i : ℕ) + T) -
        componentDifference p a d (i : ℕ) = 0 := sub_eq_zero.mpr (hall (i : ℕ))
    simp only [componentDifference, ← map_sub] at heq
    rw [← heq]
    apply congrArg (Algebra.trace (ZMod 2) (BinaryGaloisField p))
    dsimp [c, α, β]
    rw [pow_add]
    ring
  have hB (i : Fin p) : B i = β ^ (i : ℕ) := by
    simp [B]
  have hbzero : (Algebra.trace (ZMod 2) (BinaryGaloisField p)) (c * b) = 0 := by
    rw [← hbexp, Finset.mul_sum, map_sum]
    apply Finset.sum_eq_zero
    intro i hi
    rw [mul_smul_comm, map_smul, hB, hzero]
    simp
  exact hb hbzero

lemma combinedDifference_ne_zero {S : Finset ℕ}
    (hS : ∀ p ∈ S, Nat.Prime p) {a d : ℕ} (hd : 0 < d)
    (hdQ : d < S.prod fun p => 2 ^ p - 1) :
    combinedDifference S a d ≠ 0 := by
  classical
  let Q := S.prod fun p => 2 ^ p - 1
  have hQpos : 0 < Q := by
    dsimp [Q]
    apply Finset.prod_pos
    intro p hpS
    have hp2 := (hS p hpS).two_le
    have : 1 < 2 ^ p := one_lt_pow₀ (by omega) (by omega)
    omega
  have hQnd : ¬ Q ∣ d := by
    intro hdiv
    have := Nat.le_of_dvd hd hdiv
    omega
  obtain ⟨p, hpS, hpactive⟩ := exists_active_prime hS hQnd
  let T := (S.erase p).prod fun q => 2 ^ q - 1
  have hcop : Nat.Coprime (2 ^ p - 1) T :=
    mersenne_coprime_prod_erase hS hpS
  obtain ⟨i, hi⟩ := componentDifference_nonzero_somewhere
    (hS p hpS) hpactive hcop (a := a)
  intro hall
  have hall' : ∀ j, combinedDifference S a d j = 0 := by
    intro j
    exact congrFun hall j
  have hrest : (∑ q ∈ S.erase p, componentDifference q a d (i + T)) =
      ∑ q ∈ S.erase p, componentDifference q a d i := by
    apply Finset.sum_congr rfl
    intro q hq
    apply componentDifference_add_period (hS q (Finset.mem_of_mem_erase hq))
    exact Finset.dvd_prod_of_mem (fun r => 2 ^ r - 1) hq
  have hsum1 : (∑ q ∈ S, componentDifference q a d (i + T)) = 0 := by
    rw [← combinedDifference_eq_sum]
    exact hall' (i + T)
  have hsum0 : (∑ q ∈ S, componentDifference q a d i) = 0 := by
    rw [← combinedDifference_eq_sum]
    exact hall' i
  have hdec1 := Finset.sum_erase_add S
    (fun q => componentDifference q a d (i + T)) hpS
  have hdec0 := Finset.sum_erase_add S
    (fun q => componentDifference q a d i) hpS
  rw [← hdec1] at hsum1
  rw [← hdec0] at hsum0
  rw [hrest] at hsum1
  exact hi (add_left_cancel (hsum1.trans hsum0.symm))

lemma no_long_constant_run {S : Finset ℕ}
    (hS : ∀ p ∈ S, Nat.Prime p) {a d : ℕ} (hd : 0 < d)
    (hdQ : d < S.prod fun p => 2 ^ p - 1) {c : Fin 2}
    (hconst : ∀ i ≤ ∑ p ∈ S, p, combinedMSequence S (a + i * d) = c) :
    False := by
  let E := recurrenceOfMonic (combinedMinpoly S d)
  have horder : E.order ≤ ∑ p ∈ S, p := combinedMinpoly_natDegree_le S hS d
  have hzero : ∀ i < E.order, combinedDifference S a d i = 0 := by
    intro i hi
    have hiM : i + 1 ≤ ∑ p ∈ S, p := by omega
    have hc : combinedMSequence S (a + (i + 1) * d) =
        combinedMSequence S (a + i * d) :=
      (hconst (i + 1) hiM).trans (hconst i (by omega)).symm
    have hz := (combinedMSequence_eq_iff S _ _).mp hc
    have hzsub : combinedZSequence S (a + (i + 1) * d) -
        combinedZSequence S (a + i * d) = 0 := sub_eq_zero.mpr hz
    rw [combinedZSequence_sub] at hzsub
    exact hzsub
  have hall := solution_eq_zero_of_initial E (combinedDifference S a d)
    (combinedDifference_solution S a d) hzero
  exact combinedDifference_ne_zero hS hd hdQ hall

lemma bad_coloring_from_prime_set {S : Finset ℕ} {k N : ℕ}
    (hS : ∀ p ∈ S, Nat.Prime p)
    (hMpos : 0 < ∑ p ∈ S, p)
    (hk : (∑ p ∈ S, p) + 1 ≤ k)
    (hN : N ≤ (∑ p ∈ S, p) * (S.prod fun p => 2 ^ p - 1)) :
    ∃ coloring : Finset.Icc 1 N → Fin 2,
      ¬ ContainsMonoAPofLength coloring k := by
  classical
  let M := ∑ p ∈ S, p
  let Q := S.prod fun p => 2 ^ p - 1
  let coloring : Finset.Icc 1 N → Fin 2 := fun x => combinedMSequence S x.val
  refine ⟨coloring, ?_⟩
  rintro ⟨c, ap, hap, hmono⟩
  obtain ⟨a, d, heq⟩ := hap.eq
  have hkpos : 0 < k := by omega
  have hpoint (j : ℕ) (hj : j < k) :
      ∃ x ∈ ap, x.val = a + j * d := by
    have hmR : a + j * d ∈ {x | ∃ n : ℕ, ∃ (_ : (n : ℕ∞) < k),
        a + n • d = x} := by
      refine ⟨j, ?_, ?_⟩
      · exact_mod_cast hj
      · simp [nsmul_eq_mul]
    have hm : a + j * d ∈ (fun x : Finset.Icc 1 N => (x : ℕ)) '' ap :=
      heq.symm ▸ hmR
    rcases hm with ⟨x, hx, hxeq⟩
    exact ⟨x, hx, hxeq⟩
  have hdpos : 0 < d := by
    by_contra hd0
    have hd0' : d = 0 := Nat.eq_zero_of_not_pos hd0
    subst d
    have hsing : (fun x : Finset.Icc 1 N => (x : ℕ)) '' ap = {a} := by
      calc
        (fun x : Finset.Icc 1 N => (x : ℕ)) '' ap =
            {x | ∃ n : ℕ, ∃ (_ : (n : ℕ∞) < k), a + n • 0 = x} := heq
        _ = {a} := by
          ext z
          constructor
          · rintro ⟨j, hj, rfl⟩
            simp
          · intro hz
            have hza : z = a := Set.mem_singleton_iff.mp hz
            subst z
            refine ⟨0, ?_, by simp⟩
            exact_mod_cast hkpos
    have hcard : ENat.card ((fun x : Finset.Icc 1 N => (x : ℕ)) '' ap) =
        ENat.card ({a} : Set ℕ) := congrArg (fun s : Set ℕ => ENat.card s) hsing
    have hkcard : (k : ℕ∞) = 1 := by
      calc
        (k : ℕ∞) = ENat.card ((·.1) '' ap) := hap.card.symm
        _ = ENat.card ({a} : Set ℕ) := hcard
        _ = 1 := Set.encard_singleton a
    have hk1 : k = 1 := by exact_mod_cast hkcard
    omega
  have hMk : M < k := by omega
  obtain ⟨xM, hxMap, hxM⟩ := hpoint M hMk
  obtain ⟨x0, hx0ap, hx0⟩ := hpoint 0 hkpos
  have ha : 0 < a := by
    have hp : 1 ≤ x0.val ∧ x0.val ≤ N := by
      simpa using x0.property
    have hx0lo := hp.1
    rw [hx0] at hx0lo
    simpa using hx0lo
  have hxMle : a + M * d ≤ N := by
    rw [← hxM]
    exact (Finset.mem_Icc.mp xM.property).2
  have hbound : a + M * d ≤ M * Q := by
    exact hxMle.trans (by simpa [M, Q] using hN)
  have hMd : M * d < M * Q := by
    omega
  have hdQ : d < Q := by
    exact Nat.lt_of_mul_lt_mul_left hMd
  apply no_long_constant_run hS hdpos hdQ (c := c)
  intro i hi
  have hik : i < k := by
    omega
  obtain ⟨x, hxap, hx⟩ := hpoint i hik
  change combinedMSequence S (a + i * d) = c
  rw [← hx]
  exact hmono x hxap




@[category research open, AMS 11]
theorem erdos_138.variants.dvd_two_pow :
    erdos_138_variants_dvd_two_pow_statement := by
  rw [tendsto_ratio_iff_eventually_bad_coloring]
  intro n
  filter_upwards [eventually_ge_atTop (8 * (n + 1) + 2)] with k hk
  obtain ⟨S, hS, hsum⟩ := exists_distinct_prime_sum_aux (k - 1)
  let M := ∑ p ∈ S, p
  let Q := S.prod fun p => 2 ^ p - 1
  have hk3 : 3 ≤ k := by omega
  have hMlow : k - 2 ≤ M := by
    dsimp [M]
    rcases hsum with hsum | hsum <;> omega
  have hMpos : 0 < M := by omega
  have hpow := pow_sum_le_two_mul_prod_mersenne S hS
  have hpowlow : 2 ^ (k - 2) ≤ 2 ^ M :=
    Nat.pow_le_pow_right (by omega) hMlow
  have htwo : 2 ^ (k - 2) ≤ 2 * Q := by
    exact hpowlow.trans (by simpa [M, Q] using hpow)
  have hpowsucc : 2 ^ (k - 2) = 2 * 2 ^ (k - 3) := by
    have he : k - 2 = (k - 3) + 1 := by omega
    rw [he, pow_add]
    ring
  have hQlow : 2 ^ (k - 3) ≤ Q := by
    rw [hpowsucc] at htwo
    exact Nat.le_of_mul_le_mul_left htwo (by omega)
  have hcoef : 8 * (n + 1) ≤ k - 2 := by omega
  have hpow8 : 2 ^ k = 8 * 2 ^ (k - 3) := by
    calc
      2 ^ k = 2 ^ ((k - 3) + 3) := by congr 1 <;> omega
      _ = 8 * 2 ^ (k - 3) := by rw [pow_add]; ring
  have hlarge : (n + 1) * 2 ^ k ≤ M * Q := by
    rw [hpow8]
    calc
      (n + 1) * (8 * 2 ^ (k - 3)) =
          (8 * (n + 1)) * 2 ^ (k - 3) := by ring
      _ ≤ (k - 2) * 2 ^ (k - 3) :=
        Nat.mul_le_mul_right (2 ^ (k - 3)) hcoef
      _ ≤ M * Q := Nat.mul_le_mul hMlow hQlow
  apply bad_coloring_from_prime_set hS (by simpa [M] using hMpos)
  · dsimp [M]
    rcases hsum with hsum | hsum <;> omega
  · have hsub : (n + 1) * 2 ^ k - 1 ≤ M * Q :=
      (Nat.sub_le ((n + 1) * 2 ^ k) 1).trans hlarge
    simpa [M, Q] using hsub
