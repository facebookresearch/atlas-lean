/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Rat.Defs
public import MathlibExt.NumberTheory.Recurrences.LucasSequenceFirstKind
import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.LinearCombination

@[expose] public section
namespace MetaMathlibExt

/-- Addition formula for the fundamental Lucas sequence. -/
private lemma U_add (P Q : ℤ) (U : ℕ → ℤ)
    (hU0 : U 0 = 0) (hU1 : U 1 = 1)
    (hUrec : ∀ n : ℕ, U (n + 2) = P * U (n + 1) - Q * U n)
    (x y : ℕ) (hx : 1 ≤ x) :
    U (x + y) = U x * U (y + 1) - Q * U (x - 1) * U y := by
  have hx1 : x - 1 + 1 = x := Nat.sub_add_cancel hx
  have hx2 : x - 1 + 2 = x + 1 := by omega
  have key : ∀ y : ℕ, (U x * U (y + 1) - Q * U (x - 1) * U y = U (x + y)) ∧
      (U x * U (y + 2) - Q * U (x - 1) * U (y + 1) = U (x + (y + 1))) := by
    intro y
    induction y with
    | zero =>
      refine ⟨?_, ?_⟩
      · simp [hU0, hU1]
      · have h2 : U 2 = P * U 1 - Q * U 0 := hUrec 0
        have hxU : U (x + 1) = P * U x - Q * U (x - 1) := by
          have h := hUrec (x - 1)
          rwa [hx2, hx1] at h
        show U x * U 2 - Q * U (x - 1) * U 1 = U (x + 1)
        rw [h2, hU0, hU1, hxU]
        ring
    | succ y ih =>
      obtain ⟨ih0, ih1⟩ := ih
      refine ⟨ih1, ?_⟩
      have r1 : U (y + 3) = P * U (y + 2) - Q * U (y + 1) := hUrec (y + 1)
      have r2 : U (x + y + 2) = P * U (x + y + 1) - Q * U (x + y) := hUrec (x + y)
      have ry : U (y + 2) = P * U (y + 1) - Q * U y := hUrec y
      have eJ : x + (y + 1) = x + y + 1 := by omega
      rw [eJ] at ih1
      show U x * U (y + 3) - Q * U (x - 1) * U (y + 2) = U (x + y + 2)
      linear_combination U x * r1 + P * ih1 - Q * ih0 - r2 - Q * U (x - 1) * ry
  exact (key y).1.symm

/-- The Lucas sequence is a divisibility sequence. -/
private lemma U_dvd (P Q : ℤ) (U : ℕ → ℤ)
    (hU0 : U 0 = 0) (hU1 : U 1 = 1)
    (hUrec : ∀ n : ℕ, U (n + 2) = P * U (n + 1) - Q * U n)
    (m n : ℕ) (hm : 1 ≤ m) (h : m ∣ n) : U m ∣ U n := by
  obtain ⟨k, rfl⟩ := h
  suffices ∀ k : ℕ, U m ∣ U (m * k) by exact this k
  intro k
  induction k with
  | zero => simp [hU0]
  | succ k ih =>
    have e : m * (k + 1) = m + m * k := by ring
    rw [e]
    have hadd := U_add P Q U hU0 hU1 hUrec m (m * k) hm
    rw [hadd]
    exact dvd_sub (dvd_mul_right _ _) (dvd_mul_of_dvd_right ih _)

/-- Each term is congruent to a power of `P` modulo `Q`. -/
private lemma U_succ_sub_pow (P Q : ℤ) (U : ℕ → ℤ)
    (hU1 : U 1 = 1)
    (hUrec : ∀ n : ℕ, U (n + 2) = P * U (n + 1) - Q * U n) (k : ℕ) :
    Q ∣ U (k + 1) - P ^ k := by
  induction k with
  | zero =>
    show Q ∣ U 1 - P ^ 0
    simp [hU1]
  | succ n ih =>
    obtain ⟨t, ht⟩ := ih
    refine ⟨P * t - U n, ?_⟩
    show U (n + 2) - P ^ (n + 1) = Q * (P * t - U n)
    have h := hUrec n
    rw [h]
    linear_combination P * ht

/-- Cassini-style identity for the Lucas sequence. -/
private lemma U_cassini (P Q : ℤ) (U : ℕ → ℤ)
    (hU0 : U 0 = 0) (hU1 : U 1 = 1)
    (hUrec : ∀ n : ℕ, U (n + 2) = P * U (n + 1) - Q * U n) (m : ℕ) :
    U (m + 1) ^ 2 - U (m + 2) * U m = Q ^ m := by
  induction m with
  | zero =>
    have h2 : U 2 = P * U 1 - Q * U 0 := hUrec 0
    show U 1 ^ 2 - U 2 * U 0 = Q ^ 0
    simp [hU0, hU1, h2]
  | succ m ihm =>
    have r1 := hUrec m
    have r2 : U (m + 3) = P * U (m + 2) - Q * U (m + 1) := hUrec (m + 1)
    show U (m + 2) ^ 2 - U (m + 3) * U (m + 1) = Q ^ (m + 1)
    linear_combination U (m + 2) * r1 + Q * ihm - U (m + 1) * r2

/-- Consecutive terms of the Lucas sequence are coprime. -/
private lemma U_coprime_succ (P Q : ℤ) (U : ℕ → ℤ)
    (hU0 : U 0 = 0) (hU1 : U 1 = 1)
    (hUrec : ∀ n : ℕ, U (n + 2) = P * U (n + 1) - Q * U n)
    (hreg : Int.gcd P Q = 1) (n : ℕ) :
    IsCoprime (U n) (U (n + 1)) := by
  have hPQ : IsCoprime P Q := Int.isCoprime_iff_gcd_eq_one.mpr hreg
  have hsub : Q ∣ U (n + 1) - P ^ n := U_succ_sub_pow P Q U hU1 hUrec n
  obtain ⟨t, ht⟩ := hsub
  obtain ⟨a, b, hab⟩ := hPQ.pow_left (m := n)
  have h1 : IsCoprime (U (n + 1)) Q := by
    refine ⟨a, b - a * t, ?_⟩
    linear_combination hab + a * ht
  have h2 : IsCoprime (U (n + 1)) (Q ^ n) := h1.pow_right
  have hcasn := U_cassini P Q U hU0 hU1 hUrec n
  rw [← hcasn] at h2
  obtain ⟨c, d, hcd⟩ := h2
  refine ⟨-d * U (n + 2), c + d * U (n + 1), ?_⟩
  linear_combination hcd

/-- Exact characterization of prime-power divisibility in the Lucas sequence:
    `(p:ℤ)^e ∣ U k` iff the minimal such index divides `k`. -/
private lemma rank_aux (P Q : ℤ) (U : ℕ → ℤ)
    (hU0 : U 0 = 0) (hU1 : U 1 = 1)
    (hUrec : ∀ n : ℕ, U (n + 2) = P * U (n + 1) - Q * U n)
    (hreg : Int.gcd P Q = 1)
    (p : ℕ) (e : ℕ)
    (hex : ∃ m : ℕ, 1 ≤ m ∧ (p : ℤ) ^ e ∣ U m) :
    ∃ z : ℕ, 1 ≤ z ∧ ∀ k : ℕ, 1 ≤ k → ((p : ℤ) ^ e ∣ U k ↔ z ∣ k) := by
  refine ⟨Nat.find hex, (Nat.find_spec hex).1, ?_⟩
  have hzmin : ∀ m : ℕ, 1 ≤ m → (p : ℤ) ^ e ∣ U m → Nat.find hex ≤ m :=
    fun m hm hd => Nat.find_min' hex ⟨hm, hd⟩
  have hzdvd : (p : ℤ) ^ e ∣ U (Nat.find hex) := (Nat.find_spec hex).2
  have hz1 : 1 ≤ Nat.find hex := (Nat.find_spec hex).1
  intro k hk
  constructor
  · intro hdiv
    have hkz : k = Nat.find hex * (k / Nat.find hex) + k % Nat.find hex :=
      (Nat.div_add_mod k (Nat.find hex)).symm
    rcases Nat.eq_zero_or_pos (k % Nat.find hex) with ht0 | htpos
    · exact Nat.dvd_of_mod_eq_zero ht0
    · have hkx : k = (k % Nat.find hex) + Nat.find hex * (k / Nat.find hex) := by
        rw [add_comm]; exact hkz
      have hUxz : (p : ℤ) ^ e ∣ U (Nat.find hex * (k / Nat.find hex)) :=
        dvd_trans hzdvd (U_dvd P Q U hU0 hU1 hUrec _ _ hz1
          (dvd_mul_right _ _))
      have hadd := U_add P Q U hU0 hU1 hUrec (k % Nat.find hex)
        (Nat.find hex * (k / Nat.find hex)) htpos
      rw [← hkx] at hadd
      have hB : (p : ℤ) ^ e ∣ Q * U (k % Nat.find hex - 1)
          * U (Nat.find hex * (k / Nat.find hex)) :=
        dvd_mul_of_dvd_right hUxz _
      have hUk : (p : ℤ) ^ e ∣ U (k % Nat.find hex)
          * U (Nat.find hex * (k / Nat.find hex) + 1)
          - Q * U (k % Nat.find hex - 1) * U (Nat.find hex * (k / Nat.find hex)) := by
        rw [← hadd]; exact hdiv
      have hA := dvd_add hUk hB
      rw [sub_add_cancel] at hA
      rw [mul_comm (U (k % Nat.find hex)) _] at hA
      obtain ⟨u, v, huv⟩ := U_coprime_succ P Q U hU0 hU1 hUrec hreg
        (Nat.find hex * (k / Nat.find hex))
      obtain ⟨w, hw⟩ := hUxz
      have hcopPe : IsCoprime ((p : ℤ) ^ e)
          (U (Nat.find hex * (k / Nat.find hex) + 1)) :=
        ⟨u * w, v, by linear_combination huv - u * hw⟩
      have hUt := hcopPe.dvd_of_dvd_mul_left hA
      have hle := hzmin (k % Nat.find hex) htpos hUt
      have hlt : k % Nat.find hex < Nat.find hex :=
        Nat.mod_lt _ (by omega)
      omega
  · intro hzk
    exact dvd_trans hzdvd (U_dvd P Q U hU0 hU1 hUrec _ _ hz1 hzk)

/-- Successor step for counting multiples. -/
private lemma div_succ_eq (z M : ℕ) (hz : 1 ≤ z) :
    (M + 1) / z = M / z + (if z ∣ M + 1 then 1 else 0) := by
  have hzz : 0 < z := by omega
  have e3 : (M + 1) / z = (M % z + 1) / z + M / z := by
    have hmod := Nat.div_add_mod M z
    have hme : M + 1 = (M % z + 1) + z * (M / z) := by omega
    rw [hme, Nat.add_mul_div_left _ _ hzz]
  by_cases h : z ∣ M + 1
  · rw [ite_eq_left h]
    have emod1 : (M + 1) % z = 0 := Nat.dvd_iff_mod_eq_zero.mp h
    have hmod := Nat.div_add_mod M z
    have hmodz : (M % z + 1) % z = 0 := by
      have hme : M + 1 = z * (M / z) + (M % z + 1) := by omega
      rw [hme, add_comm (z * (M / z)) _, Nat.add_mul_mod_self_left] at emod1
      exact emod1
    have heq : M % z + 1 = z := by
      have hdvd : z ∣ M % z + 1 := Nat.dvd_iff_mod_eq_zero.mpr hmodz
      have hge := Nat.le_of_dvd (by omega) hdvd
      have hle : M % z + 1 ≤ z := by
        have hlt := Nat.mod_lt M hzz
        omega
      omega
    rw [e3, heq, Nat.div_self hzz]
    exact add_comm _ _
  · rw [ite_eq_right h]
    have e0 : (M % z + 1) / z = 0 := by
      apply Nat.div_eq_of_lt
      by_contra hlt
      have hlt : z ≤ M % z + 1 := le_of_not_gt hlt
      have hle : M % z + 1 ≤ z := by
        have hlt2 := Nat.mod_lt M hzz
        omega
      have heq : M % z + 1 = z := by omega
      have hmod := Nat.div_add_mod M z
      have hme : M + 1 = z * (M / z + 1) := by
        have r : z * (M / z + 1) = z * (M / z) + z := by ring
        omega
      have hdvd : z ∣ M + 1 := by
        rw [hme]
        exact dvd_mul_right z _
      exact h hdvd
    rw [e3, e0, zero_add, add_zero]

/-- Number of multiples of `z` in `Icc 1 M`. -/
private lemma card_filter_dvd_Icc_one (z M : ℕ) (hz : 1 ≤ z) :
    ((Finset.Icc 1 M).filter (fun k => z ∣ k)).card = M / z := by
  induction M with
  | zero =>
    rw [Finset.Icc_eq_empty (by omega), Finset.filter_empty, Finset.card_empty,
      Nat.zero_div]
  | succ M ih =>
    have hunion : Finset.Icc 1 (M + 1) = insert (M + 1) (Finset.Icc 1 M) := by
      ext x
      simp only [Finset.mem_insert, Finset.mem_Icc]
      omega
    rw [hunion, Finset.filter_insert, div_succ_eq z M hz]
    by_cases h : z ∣ M + 1
    · rw [ite_eq_left h, ite_eq_left h]
      have hnem : M + 1 ∉ (Finset.Icc 1 M).filter (fun k => z ∣ k) := by
        intro hmem
        rw [Finset.mem_filter, Finset.mem_Icc] at hmem
        omega
      rw [Finset.card_insert_of_notMem hnem, ih]
    · rw [ite_eq_right h, ite_eq_right h, ih, add_zero]

/-- Sum of divisibility indicators over a range. -/
private lemma sum_range_dvd_eq (z n : ℕ) (hz : 1 ≤ z) :
    ∑ j ∈ Finset.range n, (if z ∣ j + 1 then (1 : ℕ) else 0) = n / z := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, div_succ_eq z n hz]

/-- Sum of divisibility indicators over an interval. -/
private lemma sum_Icc_dvd_eq (z s m : ℕ) (hz : 1 ≤ z) :
    ∑ k ∈ Finset.Icc (s + 1) (s + m), (if z ∣ k then (1 : ℕ) else 0)
      = (s + m) / z - s / z := by
  have hunion : Finset.Icc 1 (s + m)
      = Finset.Icc 1 s ∪ Finset.Icc (s + 1) (s + m) := by
    ext x
    simp only [Finset.mem_union, Finset.mem_Icc]
    omega
  have hdisj_f : Disjoint ((Finset.Icc 1 s).filter (fun k => z ∣ k))
      ((Finset.Icc (s + 1) (s + m)).filter (fun k => z ∣ k)) := by
    rw [Finset.disjoint_left]
    intro a ha hb
    rw [Finset.mem_filter, Finset.mem_Icc] at ha hb
    omega
  have hcard := card_filter_dvd_Icc_one z (s + m) hz
  rw [hunion, Finset.filter_union,
    Finset.card_union_of_disjoint hdisj_f] at hcard
  rw [card_filter_dvd_Icc_one z s hz] at hcard
  have hfin : ∑ k ∈ Finset.Icc (s + 1) (s + m), (if z ∣ k then (1 : ℕ) else 0)
      = ((Finset.Icc (s + 1) (s + m)).filter (fun k => z ∣ k)).card := by
    rw [Finset.card_filter]
  rw [hfin]
  omega

/-- Key floor inequality: multiples of `z` up to `n`, versus those in
    `(s, s + n - 1]` plus a possible contribution from `r`. -/
private lemma floor_key (z s n r a : ℕ) (hz : 1 ≤ z) (hn : 1 ≤ n)
    (hs : s = (a - 1) * n + r) :
    n / z ≤ (if z ∣ r then 1 else 0) + ((s + n - 1) / z - s / z) := by
  have hzz : 0 < z := by omega
  have e1 : s = z * (s / z) + s % z := (Nat.div_add_mod s z).symm
  have e2 : n = z * (n / z) + n % z := (Nat.div_add_mod n z).symm
  have b1 : s % z < z := Nat.mod_lt _ hzz
  have b2 : n % z < z := Nat.mod_lt _ hzz
  by_cases hT : s % z + n % z = 0
  · have m1 : s % z = 0 := by omega
    have m2 : n % z = 0 := by omega
    have ds : z ∣ s := Nat.dvd_iff_mod_eq_zero.mpr m1
    have dn : z ∣ n := Nat.dvd_iff_mod_eq_zero.mpr m2
    have hr : z ∣ r := by
      have hrr : r = s - (a - 1) * n := by omega
      rw [hrr]
      exact Nat.dvd_sub ds (dvd_mul_of_dvd_right dn (a - 1))
    rw [ite_eq_left hr]
    have hQ2 : 1 ≤ n / z := by
      have hzz2 : z * (n / z) = n := by omega
      by_contra hlt
      have hlt : n / z < 1 := lt_of_not_ge hlt
      rw [Nat.lt_one_iff.mp hlt, Nat.mul_zero] at hzz2
      omega
    have hdiv : (s + n - 1) / z = s / z + n / z - 1 := by
      have hsn : s + n = z * (s / z + n / z) := by
        have r : z * (s / z + n / z) = z * (s / z) + z * (n / z) := by ring
        omega
      have hBnn : 0 ≤ s / z := Nat.zero_le _
      have hK : 1 ≤ s / z + n / z := by omega
      have hrep : s + n - 1 = z * (s / z + n / z - 1) + (z - 1) := by
        have hK1 : s / z + n / z - 1 + 1 = s / z + n / z := Nat.sub_add_cancel hK
        have hmul : z * (s / z + n / z - 1) + z = z * (s / z + n / z) := by
          calc z * (s / z + n / z - 1) + z
              = z * (s / z + n / z - 1) + z * 1 := by rw [mul_one]
            _ = z * (s / z + n / z - 1 + 1) := by rw [mul_add]
            _ = z * (s / z + n / z) := by rw [hK1]
        omega
      rw [hrep, add_comm (z * (s / z + n / z - 1)) _,
        Nat.add_mul_div_left _ _ hzz,
        Nat.div_eq_of_lt (show z - 1 < z by omega), zero_add]
    have eA : (s + n - 1) / z - s / z = n / z - 1 := by
      rw [hdiv]
      have t1 : s / z + n / z - 1 = s / z + (n / z - 1) := Nat.add_sub_assoc hQ2 _
      rw [t1, Nat.add_sub_cancel_left]
    have hfin : n / z = 1 + ((s + n - 1) / z - s / z) := by
      calc n / z = 1 + (n / z - 1) := (Nat.add_sub_cancel' hQ2).symm
        _ = 1 + ((s + n - 1) / z - s / z) := by rw [eA]
    exact le_of_eq hfin
  · have hT : 0 < s % z + n % z := Nat.pos_of_ne_zero hT
    have hsn : s + n - 1 = z * (s / z + n / z) + (s % z + n % z - 1) := by
      have r : z * (s / z + n / z) = z * (s / z) + z * (n / z) := by ring
      omega
    have hge : s / z + n / z ≤ (s + n - 1) / z := by
      have hle : z * (s / z + n / z) / z
          ≤ (z * (s / z + n / z) + (s % z + n % z - 1)) / z :=
        Nat.div_le_div_right (Nat.le_add_right _ _)
      rw [Nat.mul_div_cancel_left _ hzz] at hle
      rw [hsn]
      exact hle
    have hle2 : n / z ≤ (s + n - 1) / z - s / z :=
      Nat.le_sub_of_add_le (by rw [add_comm]; exact hge)
    calc n / z ≤ (s + n - 1) / z - s / z := hle2
      _ ≤ (if z ∣ r then 1 else 0) + ((s + n - 1) / z - s / z) :=
        Nat.le_add_left _ _

/-- Valuation of a finite product. -/
private lemma padic_prod (p : ℕ) (hp : p.Prime) (s : Finset ℕ) (f : ℕ → ℕ)
    (hf : ∀ x ∈ s, f x ≠ 0) :
    padicValNat p (∏ x ∈ s, f x) = ∑ x ∈ s, padicValNat p (f x) := by
  haveI : Fact p.Prime := ⟨hp⟩
  induction s using Finset.induction with
  | empty => simp
  | insert a s has ih =>
    rw [Finset.prod_insert has, Finset.sum_insert has,
      padicValNat.mul (hf _ (Finset.mem_insert_self _ _))
        (Finset.prod_ne_zero_iff.mpr (fun x hx => hf x (Finset.mem_insert_of_mem hx))),
      ih (fun x hx => hf x (Finset.mem_insert_of_mem hx))]

/-- Valuation as a sum of prime-power indicators. -/
private lemma padic_eq_sum (p m E : ℕ) (hp : p.Prime) (hm : m ≠ 0)
    (hE : padicValNat p m ≤ E) :
    padicValNat p m
      = ∑ e ∈ Finset.range (E + 1), (if 1 ≤ e ∧ p ^ e ∣ m then (1 : ℕ) else 0) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hiff : ∀ e : ℕ, (1 ≤ e ∧ p ^ e ∣ m) ↔ e ∈ Finset.Icc 1 (padicValNat p m) := by
    intro e
    rw [Finset.mem_Icc]
    constructor
    · intro ⟨h1, hd⟩
      exact ⟨h1, (padicValNat_dvd_iff_le hm).mp hd⟩
    · intro ⟨h1, h2⟩
      exact ⟨h1, (padicValNat_dvd_iff_le hm).mpr h2⟩
  have hsum : ∑ e ∈ Finset.range (E + 1), (if 1 ≤ e ∧ p ^ e ∣ m then (1 : ℕ) else 0)
      = ∑ e ∈ Finset.range (E + 1),
        (if e ∈ Finset.Icc 1 (padicValNat p m) then (1 : ℕ) else 0) := by
    apply Finset.sum_congr rfl
    intro e _
    by_cases h : 1 ≤ e ∧ p ^ e ∣ m
    · rw [ite_eq_left h, ite_eq_left ((hiff e).mp h)]
    · rw [ite_eq_right h, ite_eq_right (fun h2 => h ((hiff e).mpr h2))]
  have hfil : (Finset.range (E + 1)).filter
        (fun e => e ∈ Finset.Icc 1 (padicValNat p m))
      = Finset.Icc 1 (padicValNat p m) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
    constructor
    · intro ⟨_, h1, h2⟩
      exact ⟨h1, h2⟩
    · intro ⟨h1, h2⟩
      exact ⟨by omega, h1, h2⟩
  rw [hsum, ← Finset.card_filter, hfil, Nat.card_Icc]
  simp

/-- From natural divisibility to integer divisibility for prime powers. -/
private lemma natAbs_dvd_to_dvd (p e : ℕ) (U : ℕ → ℤ) (k : ℕ)
    (h : p ^ e ∣ (U k).natAbs) : (p : ℤ) ^ e ∣ U k := by
  have h1 : ((p ^ e : ℕ) : ℤ).natAbs ∣ (U k).natAbs := by
    rw [Int.natAbs_natCast]
    exact h
  have h2 := Int.natAbs_dvd_natAbs.mp h1
  have h3 : ((p : ℤ) ^ e) = (((p ^ e : ℕ)) : ℤ) := by push_cast; ring
  rwa [h3]

/-- From integer divisibility to natural divisibility for prime powers. -/
private lemma dvd_to_natAbs_dvd (p e : ℕ) (U : ℕ → ℤ) (k : ℕ)
    (h : (p : ℤ) ^ e ∣ U k) : p ^ e ∣ (U k).natAbs := by
  have h2 : ((p : ℤ) ^ e) = (((p ^ e : ℕ)) : ℤ) := by push_cast; ring
  rw [h2] at h
  have h3 := Int.natAbs_dvd_natAbs.mpr h
  rwa [Int.natAbs_natCast] at h3

/-- The key divisibility in naturals. -/
private lemma key_dvd (P Q : ℤ) (U : ℕ → ℤ)
    (hU0 : U 0 = 0) (hU1 : U 1 = 1)
    (hUrec : ∀ n : ℕ, U (n + 2) = P * U (n + 1) - Q * U n)
    (hreg : Int.gcd P Q = 1)
    (hnondeg : ∀ n : ℕ, n ≥ 1 → U n ≠ 0)
    (r a n s : ℕ) (hr : r ≥ 1) (ha : a ≥ 2) (hn : n ≥ 1)
    (hs : s = (a - 1) * n + r) :
    (∏ j ∈ Finset.range n, (U (j + 1)).natAbs)
      ∣ (U r).natAbs * ∏ k ∈ Finset.Icc (s + 1) (s + n - 1), (U k).natAbs := by
  have hV : ∀ k : ℕ, 1 ≤ k → (U k).natAbs ≠ 0 := by
    intro k hk hcon
    exact hnondeg k hk (Int.natAbs_eq_zero.mp hcon)
  have hBf : ∀ j ∈ Finset.range n, (U (j + 1)).natAbs ≠ 0 :=
    fun j _ => hV (j + 1) (by omega)
  have hCf : ∀ k ∈ Finset.Icc (s + 1) (s + n - 1), (U k).natAbs ≠ 0 := by
    intro k hk
    rw [Finset.mem_Icc] at hk
    exact hV k (by omega)
  have hVr : (U r).natAbs ≠ 0 := hV r (by omega)
  have hBpos : 0 < ∏ j ∈ Finset.range n, (U (j + 1)).natAbs :=
    Nat.pos_of_ne_zero (Finset.prod_ne_zero_iff.mpr hBf)
  have hCpos : 0 < (U r).natAbs
      * ∏ k ∈ Finset.Icc (s + 1) (s + n - 1), (U k).natAbs :=
    Nat.pos_of_ne_zero (mul_ne_zero hVr (Finset.prod_ne_zero_iff.mpr hCf))
  have dvdB : ∀ j ∈ Finset.range n,
      (U (j + 1)).natAbs ∣ ∏ j ∈ Finset.range n, (U (j + 1)).natAbs :=
    fun j hj => Finset.dvd_prod_of_mem _ hj
  have dvdC : ∀ k ∈ Finset.Icc (s + 1) (s + n - 1),
      (U k).natAbs ∣ (U r).natAbs
        * ∏ k ∈ Finset.Icc (s + 1) (s + n - 1), (U k).natAbs :=
    fun k hk => dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem _ hk) _
  set B := ∏ j ∈ Finset.range n, (U (j + 1)).natAbs with hBdef
  set C := (U r).natAbs * ∏ k ∈ Finset.Icc (s + 1) (s + n - 1), (U k).natAbs
    with hCdef
  rw [← Nat.factorization_le_iff_dvd (ne_of_gt hBpos) (ne_of_gt hCpos),
    Finsupp.le_iff]
  intro p hpmem
  have hprime : p.Prime := by
    have hmem : p ∈ B.primeFactors := by
      rw [← Nat.support_factorization]
      exact hpmem
    exact Nat.prime_of_mem_primeFactors hmem
  haveI : Fact p.Prime := ⟨hprime⟩
  rw [Nat.factorization_def _ hprime, Nat.factorization_def _ hprime]
  rw [padic_prod p hprime (Finset.range n) _ hBf,
    padicValNat.mul hVr (Finset.prod_ne_zero_iff.mpr hCf),
    padic_prod p hprime (Finset.Icc (s + 1) (s + n - 1)) _ hCf]
  have hbound : ∀ m : ℕ, m ≠ 0 → m ≤ B + C → padicValNat p m ≤ B + C := by
    intro m hm0 hmE
    have h1 : p ^ padicValNat p m ∣ m := pow_padicValNat_dvd
    have h2 : p ^ padicValNat p m ≤ m :=
      Nat.le_of_dvd (Nat.pos_of_ne_zero hm0) h1
    have h3 : padicValNat p m ≤ p ^ padicValNat p m := by
      rcases eq_or_ne (padicValNat p m) 0 with h0 | h0
      · rw [h0]
        exact Nat.zero_le _
      · have hpp2 : 2 ≤ p := hprime.two_le
        have hlt : padicValNat p m < 2 ^ padicValNat p m := Nat.lt_two_pow_self
        have hle : 2 ^ padicValNat p m ≤ p ^ padicValNat p m :=
          Nat.pow_le_pow_left hpp2 _
        omega
    omega
  have hexpand : ∀ m : ℕ, m ≠ 0 → m ≤ B + C → padicValNat p m
      = ∑ e ∈ Finset.range (B + C + 1),
        (if 1 ≤ e ∧ p ^ e ∣ m then (1 : ℕ) else 0) :=
    fun m hm0 hmE => padic_eq_sum p m (B + C) hprime hm0 (hbound m hm0 hmE)
  have hBL : (∑ j ∈ Finset.range n, padicValNat p ((U (j + 1)).natAbs))
      = ∑ e ∈ Finset.range (B + C + 1), ∑ j ∈ Finset.range n,
        (if 1 ≤ e ∧ p ^ e ∣ (U (j + 1)).natAbs then (1 : ℕ) else 0) := by
    calc (∑ j ∈ Finset.range n, padicValNat p ((U (j + 1)).natAbs))
        = ∑ j ∈ Finset.range n, ∑ e ∈ Finset.range (B + C + 1),
            (if 1 ≤ e ∧ p ^ e ∣ (U (j + 1)).natAbs then (1 : ℕ) else 0) :=
          Finset.sum_congr rfl (fun j hj =>
            hexpand _ (hBf j hj) (le_trans (Nat.le_of_dvd hBpos (dvdB j hj))
              (Nat.le_add_right _ _)))
      _ = _ := Finset.sum_comm
  have eR : padicValNat p ((U r).natAbs)
      = ∑ e ∈ Finset.range (B + C + 1),
        (if 1 ≤ e ∧ p ^ e ∣ (U r).natAbs then (1 : ℕ) else 0) :=
    hexpand _ hVr (le_trans (Nat.le_of_dvd hCpos (dvd_mul_right _ _))
      (Nat.le_add_left _ _))
  have eK : (∑ k ∈ Finset.Icc (s + 1) (s + n - 1), padicValNat p ((U k).natAbs))
      = ∑ k ∈ Finset.Icc (s + 1) (s + n - 1), ∑ e ∈ Finset.range (B + C + 1),
        (if 1 ≤ e ∧ p ^ e ∣ (U k).natAbs then (1 : ℕ) else 0) :=
    Finset.sum_congr rfl (fun k hk =>
      hexpand _ (hCf k hk) (le_trans (Nat.le_of_dvd hCpos (dvdC k hk))
        (Nat.le_add_left _ _)))
  have hBR : padicValNat p ((U r).natAbs)
        + ∑ k ∈ Finset.Icc (s + 1) (s + n - 1), padicValNat p ((U k).natAbs)
      = ∑ e ∈ Finset.range (B + C + 1),
        ((if 1 ≤ e ∧ p ^ e ∣ (U r).natAbs then (1 : ℕ) else 0)
          + ∑ k ∈ Finset.Icc (s + 1) (s + n - 1),
            (if 1 ≤ e ∧ p ^ e ∣ (U k).natAbs then (1 : ℕ) else 0)) := by
    rw [eR, eK,
      Finset.sum_comm (s := Finset.Icc (s + 1) (s + n - 1))
        (t := Finset.range (B + C + 1)),
      ← Finset.sum_add_distrib]
  rw [hBL, hBR]
  apply Finset.sum_le_sum
  intro e _
  by_cases he1 : 1 ≤ e
  · by_cases hex_e : ∃ m : ℕ, 1 ≤ m ∧ (p : ℤ) ^ e ∣ U m
    · obtain ⟨z, hz1, hchar⟩ := rank_aux P Q U hU0 hU1 hUrec hreg p e hex_e
      have ind_j : ∀ j ∈ Finset.range n,
          (if 1 ≤ e ∧ p ^ e ∣ (U (j + 1)).natAbs then (1 : ℕ) else 0)
          = (if z ∣ j + 1 then (1 : ℕ) else 0) := by
        intro j _
        by_cases hj : p ^ e ∣ (U (j + 1)).natAbs
        · have hzjdvd : z ∣ j + 1 :=
            (hchar (j + 1) (by omega)).mp (natAbs_dvd_to_dvd p e U (j + 1) hj)
          rw [ite_eq_left ⟨he1, hj⟩, ite_eq_left hzjdvd]
        · have hnz : ¬ (p : ℤ) ^ e ∣ U (j + 1) :=
            fun hcon => hj (dvd_to_natAbs_dvd p e U (j + 1) hcon)
          have hnz2 : ¬ z ∣ j + 1 :=
            fun hcon => hnz ((hchar (j + 1) (by omega)).mpr hcon)
          rw [ite_eq_right (fun hcon => hj hcon.2), ite_eq_right hnz2]
      have ind_r : (if 1 ≤ e ∧ p ^ e ∣ (U r).natAbs then (1 : ℕ) else 0)
          = (if z ∣ r then (1 : ℕ) else 0) := by
        by_cases hr2 : p ^ e ∣ (U r).natAbs
        · have hzrdvd : z ∣ r :=
            (hchar r (by omega)).mp (natAbs_dvd_to_dvd p e U r hr2)
          rw [ite_eq_left ⟨he1, hr2⟩, ite_eq_left hzrdvd]
        · have hnz : ¬ (p : ℤ) ^ e ∣ U r :=
            fun hcon => hr2 (dvd_to_natAbs_dvd p e U r hcon)
          have hnz2 : ¬ z ∣ r :=
            fun hcon => hnz ((hchar r (by omega)).mpr hcon)
          rw [ite_eq_right (fun hcon => hr2 hcon.2), ite_eq_right hnz2]
      have ind_k : ∀ k ∈ Finset.Icc (s + 1) (s + n - 1),
          (if 1 ≤ e ∧ p ^ e ∣ (U k).natAbs then (1 : ℕ) else 0)
          = (if z ∣ k then (1 : ℕ) else 0) := by
        intro k hk
        rw [Finset.mem_Icc] at hk
        by_cases hk2 : p ^ e ∣ (U k).natAbs
        · have hzkdvd : z ∣ k :=
            (hchar k (by omega)).mp (natAbs_dvd_to_dvd p e U k hk2)
          rw [ite_eq_left ⟨he1, hk2⟩, ite_eq_left hzkdvd]
        · have hnz : ¬ (p : ℤ) ^ e ∣ U k :=
            fun hcon => hk2 (dvd_to_natAbs_dvd p e U k hcon)
          have hnz2 : ¬ z ∣ k :=
            fun hcon => hnz ((hchar k (by omega)).mpr hcon)
          rw [ite_eq_right (fun hcon => hk2 hcon.2), ite_eq_right hnz2]
      rw [Finset.sum_congr rfl ind_j, ind_r, Finset.sum_congr rfl ind_k,
        sum_range_dvd_eq z n hz1]
      have hIcc : Finset.Icc (s + 1) (s + n - 1)
          = Finset.Icc (s + 1) (s + (n - 1)) := by
        have hnm : s + (n - 1) = s + n - 1 := by omega
        rw [hnm]
      rw [hIcc, sum_Icc_dvd_eq z s (n - 1) hz1]
      have hnm : s + (n - 1) = s + n - 1 := by omega
      rw [hnm]
      exact floor_key z s n r a hz1 hn hs
    · have zero_j : ∀ j ∈ Finset.range n,
          (if 1 ≤ e ∧ p ^ e ∣ (U (j + 1)).natAbs then (1 : ℕ) else 0) = 0 := by
        intro j _
        rw [ite_eq_right]
        intro hcon
        apply hex_e
        exact ⟨j + 1, by omega, natAbs_dvd_to_dvd p e U (j + 1) hcon.2⟩
      have zero_r : (if 1 ≤ e ∧ p ^ e ∣ (U r).natAbs then (1 : ℕ) else 0) = 0 := by
        rw [ite_eq_right]
        intro hcon
        apply hex_e
        exact ⟨r, by omega, natAbs_dvd_to_dvd p e U r hcon.2⟩
      have zero_k : ∀ k ∈ Finset.Icc (s + 1) (s + n - 1),
          (if 1 ≤ e ∧ p ^ e ∣ (U k).natAbs then (1 : ℕ) else 0) = 0 := by
        intro k hk
        rw [Finset.mem_Icc] at hk
        rw [ite_eq_right]
        intro hcon
        apply hex_e
        exact ⟨k, by omega, natAbs_dvd_to_dvd p e U k hcon.2⟩
      rw [Finset.sum_eq_zero zero_j, zero_r, Finset.sum_eq_zero zero_k,
        add_zero]
  · have zero_j : ∀ j ∈ Finset.range n,
        (if 1 ≤ e ∧ p ^ e ∣ (U (j + 1)).natAbs then (1 : ℕ) else 0) = 0 := by
      intro j _
      rw [ite_eq_right (fun hcon => he1 hcon.1)]
    rw [Finset.sum_eq_zero zero_j]
    exact Nat.zero_le _

/-- `natAbs` of a product. -/
private lemma natAbs_prod (s : Finset ℕ) (f : ℕ → ℤ) :
    (∏ x ∈ s, f x).natAbs = ∏ x ∈ s, (f x).natAbs := by
  induction s using Finset.induction with
  | empty => simp
  | insert a s has ih =>
    rw [Finset.prod_insert has, Finset.prod_insert has, Int.natAbs_mul, ih]

/-- **Integrality of generalized Lucasnomial Fuss–Catalan numbers.** Let $P$ and $Q$ be integers
with $\gcd(P, Q) = 1$, let $(U_m)_{m \ge 0}$ be the Lucas sequence of the first kind with
parameters $P$ and $Q$, and suppose $U_m \ne 0$ for every $m \ge 1$. Then for all natural numbers
$r \ge 1$, $a \ge 2$ and $n \ge 1$, the rational number
$$\frac{U_r}{U_{(a-1)n+r}} \cdot \frac{\prod_{j=0}^{n-1} U_{an+r-1-j}}{\prod_{j=0}^{n-1} U_{j+1}}$$
is an integer; its second factor is the Lucasnomial coefficient $\binom{an+r-1}{n}_U$. -/
theorem generalized_lucasnomial_fuss_catalan_integral_general {P Q : ℤ} {U : ℕ → ℤ}
    (hU : IsLucasSequenceFirstKind P Q U) (hnondeg : ∀ n : ℕ, n ≥ 1 → U n ≠ 0)
    (hreg : Int.gcd P Q = 1) (r a : ℕ) (hr : r ≥ 1) (ha : a ≥ 2) (n : ℕ) (hn : n ≥ 1) :
    ∃ z : ℤ,
      ((U r : ℚ) / ((U ((a - 1) * n + r)) : ℚ)) *
          ((∏ j ∈ Finset.range n, ((U (a * n + r - 1 - j)) : ℚ)) /
            (∏ j ∈ Finset.range n, ((U (j + 1)) : ℚ))) =
        ((z : ℚ)) := by
  have hU0 := hU.initialZero
  have hU1 := hU.initialOne
  have hUrec := hU.recurrenceStep
  set s := (a - 1) * n + r with hsdef
  have hs : s = (a - 1) * n + r := hsdef
  have hs1 : 1 ≤ s := by omega
  have hUr : (U r : ℚ) ≠ 0 := by exact_mod_cast hnondeg r hr
  have hUs : (U s : ℚ) ≠ 0 := by exact_mod_cast hnondeg s hs1
  have hden : (∏ j ∈ Finset.range n, ((U (j + 1) : ℤ) : ℚ)) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro j _
    exact_mod_cast hnondeg (j + 1) (by omega)
  have hdiv_nat :=
    key_dvd P Q U hU0 hU1 hUrec hreg hnondeg r a n s hr ha hn hs
  have hdiv_int : (∏ j ∈ Finset.range n, U (j + 1))
      ∣ U r * ∏ k ∈ Finset.Icc (s + 1) (s + n - 1), U k := by
    rw [← Int.natAbs_dvd_natAbs, natAbs_prod, Int.natAbs_mul, natAbs_prod]
    exact hdiv_nat
  obtain ⟨c, hc⟩ := hdiv_int
  have hae : a * n = (a - 1) * n + n := by
    have h1 : a - 1 + 1 = a := by omega
    calc a * n = (a - 1 + 1) * n := by rw [h1]
      _ = (a - 1) * n + 1 * n := by rw [add_mul]
      _ = (a - 1) * n + n := by rw [one_mul]
  have hnum : (∏ j ∈ Finset.range n, ((U (a * n + r - 1 - j) : ℤ) : ℚ))
      = ∏ k ∈ Finset.Icc s (s + n - 1), ((U k : ℤ) : ℚ) := by
    have e : ∀ j ∈ Finset.range n, a * n + r - 1 - j = s + (n - 1 - j) := by
      intro j hj
      rw [Finset.mem_range] at hj
      omega
    calc (∏ j ∈ Finset.range n, ((U (a * n + r - 1 - j) : ℤ) : ℚ))
        = ∏ j ∈ Finset.range n, ((U (s + (n - 1 - j)) : ℤ) : ℚ) :=
          Finset.prod_congr rfl (fun j hj => by rw [e j hj])
      _ = ∏ j ∈ Finset.range n, ((U (s + j) : ℤ) : ℚ) :=
          Finset.prod_range_reflect (fun k => ((U (s + k) : ℤ) : ℚ)) n
      _ = ∏ k ∈ Finset.Ico s (s + n), ((U k : ℤ) : ℚ) := by
          refine Finset.prod_bij (fun j _ => s + j) ?_ ?_ ?_ ?_
          · intro j hj
            rw [Finset.mem_range] at hj
            rw [Finset.mem_Ico]
            constructor <;> omega
          · intro j1 _ j2 _ h12
            omega
          · intro k hk
            rw [Finset.mem_Ico] at hk
            refine ⟨k - s, ?_, ?_⟩
            · rw [Finset.mem_range]
              omega
            · omega
          · intro j hj
            rfl
      _ = ∏ k ∈ Finset.Icc s (s + n - 1), ((U k : ℤ) : ℚ) := by
          have hIcoIcc : Finset.Ico s (s + n)
              = Finset.Icc s (s + n - 1) := by
            ext x
            simp only [Finset.mem_Ico, Finset.mem_Icc]
            omega
          rw [hIcoIcc]
  have hsplit : (∏ k ∈ Finset.Icc s (s + n - 1), ((U k : ℤ) : ℚ))
      = ((U s : ℤ) : ℚ)
        * ∏ k ∈ Finset.Icc (s + 1) (s + n - 1), ((U k : ℤ) : ℚ) := by
    have hmem : s ∈ Finset.Icc s (s + n - 1) := by
      rw [Finset.mem_Icc]
      constructor <;> omega
    have herase : (Finset.Icc s (s + n - 1)).erase s
        = Finset.Icc (s + 1) (s + n - 1) := by
      ext x
      simp only [Finset.mem_erase, Finset.mem_Icc]
      omega
    have h := Finset.mul_prod_erase (Finset.Icc s (s + n - 1))
      (fun k => ((U k : ℤ) : ℚ)) hmem
    rw [herase] at h
    exact h.symm
  have hcQ : ((U r : ℤ) : ℚ)
        * ∏ k ∈ Finset.Icc (s + 1) (s + n - 1), ((U k : ℤ) : ℚ)
      = (∏ j ∈ Finset.range n, ((U (j + 1) : ℤ) : ℚ)) * ((c : ℤ) : ℚ) := by
    have hc' : ((((U r * ∏ k ∈ Finset.Icc (s + 1) (s + n - 1), U k : ℤ))) : ℚ)
        = (((((∏ j ∈ Finset.range n, U (j + 1)) * c : ℤ))) : ℚ) := by
      exact_mod_cast hc
    rw [Int.cast_mul, Int.cast_prod, Int.cast_mul, Int.cast_prod] at hc'
    exact hc'
  refine ⟨c, ?_⟩
  rw [hnum, hsplit]
  have hBp : (∏ j ∈ Finset.range n, ((U (j + 1) : ℤ) : ℚ)) ≠ 0 := hden
  rw [div_mul_div_comm, div_eq_iff (mul_ne_zero hUs hBp)]
  calc ((U r : ℤ) : ℚ) * (((U s : ℤ) : ℚ)
        * ∏ k ∈ Finset.Icc (s + 1) (s + n - 1), ((U k : ℤ) : ℚ))
      = ((U s : ℤ) : ℚ) * (((U r : ℤ) : ℚ)
        * ∏ k ∈ Finset.Icc (s + 1) (s + n - 1), ((U k : ℤ) : ℚ)) := by ring
    _ = ((U s : ℤ) : ℚ) * ((∏ j ∈ Finset.range n, ((U (j + 1) : ℤ) : ℚ))
        * ((c : ℤ) : ℚ)) := by rw [hcQ]
    _ = ((c : ℤ) : ℚ) * (((U s : ℤ) : ℚ)
        * ∏ j ∈ Finset.range n, ((U (j + 1) : ℤ) : ℚ)) := by ring

set_option linter.unusedVariables false in
/-- **Generalized Lucasnomial Fuss–Catalan numbers are integers (Ballot).** Let $P$ and $Q$ be
nonzero integers with $\gcd(P, Q) = 1$, and let $U : \mathbb{N} \to \mathbb{Z}$ satisfy $U_0 = 0$,
$U_1 = 1$, $U_{m+2} = P U_{m+1} - Q U_m$ for every natural number $m$, and $U_m \ne 0$ for every
$m \ge 1$. Then for all natural numbers $r \ge 1$, $a \ge 2$ and $n \ge 1$, the rational number
$$\frac{U_r}{U_{(a-1)n+r}} \cdot \frac{\prod_{j=0}^{n-1} U_{an+r-1-j}}{\prod_{j=0}^{n-1} U_{j+1}}$$
is an integer; its second factor is the Lucasnomial coefficient $\binom{an+r-1}{n}_U$.

Source: Christian Ballot, "Lucasnomial Fuss-Catalan Numbers and Related
Divisibility Questions," Journal of Integer Sequences 21 (2018), Article 18.6.5, Theorem `thm:2`,
lines 553–558, <https://cs.uwaterloo.ca/journals/JIS/VOL21/Ballot/ballot30.tex>. Fundamental Lucas
sequences, nondegeneracy, and regularity at lines 185–207; Lucasnomial coefficients at lines
215–221.
It follows from `generalized_lucasnomial_fuss_catalan_integral_general`; the hypotheses `hP` and
`hQ` are unused and keep the source's shape.
Proves `Wanted` entry `generalized_lucasnomial_fuss_catalan_integral`.
-/
theorem generalized_lucasnomial_fuss_catalan_integral (P Q : ℤ)
    (U : ℕ → ℤ) (r a : ℕ) (hP : P ≠ 0) (hQ : Q ≠ 0) (hU0 : U 0 = 0)
    (hU1 : U 1 = 1) (hUrec : ∀ n : ℕ, U (n + 2) = P * U (n + 1) - Q * U n)
    (hnondeg : ∀ n : ℕ, n ≥ 1 → U n ≠ 0) (hreg : Int.gcd P Q = 1)
    (hr : r ≥ 1) (ha : a ≥ 2) (n : ℕ) (hn : n ≥ 1) :
    ∃ z : ℤ,
      ((U r : ℚ) / ((U ((a - 1) * n + r)) : ℚ)) *
          ((∏ j ∈ Finset.range n, ((U (a * n + r - 1 - j)) : ℚ)) /
            (∏ j ∈ Finset.range n, ((U (j + 1)) : ℚ))) =
        ((z : ℚ)) := by
  exact generalized_lucasnomial_fuss_catalan_integral_general ⟨hU0, hU1, hUrec⟩ hnondeg hreg
    r a hr ha n hn

end MetaMathlibExt
