/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.PolygonalNumber
public import MathlibExt.NumberTheory.PracticalNumber
import MathlibExt.NumberTheory.PracticalPolygonalSums
import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Tactic.Ring

/-!
# Exceptions to sums of a practical number and polygonal numbers

This module proves that for `s ≥ 3` with `s ≡ 0` or `s ≡ 4 (mod 12)` there are infinitely
many positive integers not of the form `q + p_s(m)` with `q` practical, and that the number
of positive integers not of the form `q + p_t(x) + p_t(y)` grows without bound as `t` grows.

Statements from Sai Teja Somu and Duc Van Khanh Tran, *On Sums of Practical Numbers and
Polygonal Numbers*, Journal of Integer Sequences 27 (2024), Article 24.5.1
(arXiv:2403.13533). In the paper "natural number" means positive integer; practical numbers
are `MetaMathlibExt.IsPracticalNumber`. The paper's `s`-gonal number `P_s(n)` is the canonical
`Nat.polygonalNumber s n`; triangular numbers are `Nat.polygonalNumber 3 k = k (k + 1) / 2`
with `k ≥ 0` (the paper's Lemma 5, arXiv Lemma 3.3, counts `0`).
-/

namespace MetaMathlibExt

private theorem choose_succ_two (k : ℕ) : (k + 1).choose 2 = k.choose 2 + k := by
  simpa [Nat.choose_one_right, Nat.add_comm] using Nat.choose_succ_succ k 1

private theorem two_mul_choose_add (n : ℕ) : 2 * (Nat.choose n 2) + n = n ^ 2 := by
  induction n with
  | zero => decide
  | succ n ih =>
    have hpascal : Nat.choose (n + 1) 2 = Nat.choose n 2 + n :=
      choose_succ_two n
    have hsq : (n + 1) ^ 2 = n ^ 2 + 2 * n + 1 := by ring
    omega

private theorem mul_pred_add (m : ℕ) : m * (m - 1) + m = m ^ 2 := by
  cases m with
  | zero => decide
  | succ m =>
    have hsub : (m + 1) - 1 = m := Nat.add_sub_cancel _ _
    rw [hsub]
    ring

private theorem two_mul_choose_eq (n : ℕ) : 2 * Nat.choose n 2 = n * (n - 1) := by
  have h1 := two_mul_choose_add n
  have h2 := mul_pred_add n
  omega

private theorem polygonal_succ (s m : ℕ) :
    Nat.polygonalNumber s (m + 1) =
      Nat.polygonalNumber s m + (s - 2) * m + 1 := by
  have hC := choose_succ_two m
  simp only [Nat.polygonalNumber, hC]
  ring

private theorem sq_mod4_mem (m : ℕ) : m ^ 2 % 4 = 0 ∨ m ^ 2 % 4 = 1 := by
  have hm4 : m % 4 = 0 ∨ m % 4 = 1 ∨ m % 4 = 2 ∨ m % 4 = 3 := by omega
  have hpow := Nat.pow_mod m 2 4
  rcases hm4 with h | h | h | h <;> rw [hpow, h] <;> decide

private theorem sq_mod3_mem (m : ℕ) : m ^ 2 % 3 = 0 ∨ m ^ 2 % 3 = 1 := by
  have hm3 : m % 3 = 0 ∨ m % 3 = 1 ∨ m % 3 = 2 := by omega
  have hpow := Nat.pow_mod m 2 3
  rcases hm3 with h | h | h <;> rw [hpow, h] <;> decide

private theorem sq_add_mod3_mem (m : ℕ) : (m ^ 2 + m) % 3 = 0 ∨ (m ^ 2 + m) % 3 = 2 := by
  have hm3 : m % 3 = 0 ∨ m % 3 = 1 ∨ m % 3 = 2 := by omega
  have hadd := Nat.add_mod (m ^ 2) m 3
  have hpow := Nat.pow_mod m 2 3
  rcases hm3 with h | h | h <;> rw [hadd, hpow, h] <;> decide

private theorem polygonal_mod4_eq_sq (s m : ℕ) (hs4 : s % 4 = 0) (hs : 3 ≤ s) :
    Nat.polygonalNumber s m % 4 = m ^ 2 % 4 := by
  have hs2mod : (s - 2) % 4 = 2 := by omega
  have h2C := two_mul_choose_eq m
  have hmul4 : ((s - 2) * Nat.choose m 2) % 4 = (m * (m - 1)) % 4 := by
    have h1 := Nat.mul_mod (s - 2) (Nat.choose m 2) 4
    have h2 := Nat.mul_mod 2 (Nat.choose m 2) 4
    have h2mod : (2 : ℕ) % 4 = 2 := by decide
    rw [h2mod] at h2
    rw [hs2mod] at h1
    omega
  have hadd1 := Nat.add_mod ((s - 2) * Nat.choose m 2) m 4
  have hadd2 := Nat.add_mod (m * (m - 1)) m 4
  have hmp := mul_pred_add m
  unfold Nat.polygonalNumber
  omega

private theorem polygonal_mod4_mem (s m : ℕ) (hs4 : s % 4 = 0) (hs : 3 ≤ s) :
    Nat.polygonalNumber s m % 4 = 0 ∨ Nat.polygonalNumber s m % 4 = 1 := by
  have heq := polygonal_mod4_eq_sq s m hs4 hs
  have hmem := sq_mod4_mem m
  omega

private theorem polygonal_mod3_eq_sq_of_mod1 (s m : ℕ) (hs3 : s % 3 = 1) (hs : 3 ≤ s) :
    Nat.polygonalNumber s m % 3 = m ^ 2 % 3 := by
  have hs2mod : (s - 2) % 3 = 2 := by omega
  have h2C := two_mul_choose_eq m
  have hmul3 : ((s - 2) * Nat.choose m 2) % 3 = (m * (m - 1)) % 3 := by
    have h1 := Nat.mul_mod (s - 2) (Nat.choose m 2) 3
    have h2 := Nat.mul_mod 2 (Nat.choose m 2) 3
    have h2mod : (2 : ℕ) % 3 = 2 := by decide
    rw [h2mod] at h2
    rw [hs2mod] at h1
    omega
  have hadd1 := Nat.add_mod ((s - 2) * Nat.choose m 2) m 3
  have hadd2 := Nat.add_mod (m * (m - 1)) m 3
  have hmp := mul_pred_add m
  unfold Nat.polygonalNumber
  omega

private theorem polygonal_mod3_ne2_of_mod1 (s m : ℕ) (hs3 : s % 3 = 1) (hs : 3 ≤ s) :
    Nat.polygonalNumber s m % 3 ≠ 2 := by
  have heq := polygonal_mod3_eq_sq_of_mod1 s m hs3 hs
  have hmem := sq_mod3_mem m
  omega

private theorem two_mul_polygonal_eq (s m : ℕ) :
    2 * Nat.polygonalNumber s m = (s - 2) * (m * (m - 1)) + 2 * m := by
  have h2C := two_mul_choose_eq m
  calc
    2 * Nat.polygonalNumber s m
        = (s - 2) * (2 * Nat.choose m 2) + 2 * m := by
          simp only [Nat.polygonalNumber]
          ring
    _ = (s - 2) * (m * (m - 1)) + 2 * m := by rw [h2C]

private theorem add_two_mul_eq_sq_add (m : ℕ) : m * (m - 1) + 2 * m = m ^ 2 + m := by
  have h := mul_pred_add m
  omega

private theorem two_mul_polygonal_mod3 (s m : ℕ) (hs3 : s % 3 = 0) (hs : 3 ≤ s) :
    (2 * Nat.polygonalNumber s m) % 3 = 0 ∨
      (2 * Nat.polygonalNumber s m) % 3 = 2 := by
  have hs2mod : (s - 2) % 3 = 1 := by omega
  have h2P := two_mul_polygonal_eq s m
  have hX := add_two_mul_eq_sq_add m
  have hmem := sq_add_mod3_mem m
  have hmul_eq : ((s - 2) * (m * (m - 1))) % 3 = (m * (m - 1)) % 3 := by
    have hmul := Nat.mul_mod (s - 2) (m * (m - 1)) 3
    rw [hs2mod] at hmul
    have h1 : (1 * ((m * (m - 1)) % 3)) % 3 = (m * (m - 1)) % 3 := by
      rw [Nat.one_mul, Nat.mod_mod]
    rw [h1] at hmul
    exact hmul
  have heq : (2 * Nat.polygonalNumber s m) % 3 = (m ^ 2 + m) % 3 := by
    calc
      (2 * Nat.polygonalNumber s m) % 3
          = ((s - 2) * (m * (m - 1)) + 2 * m) % 3 := by rw [h2P]
      _ = ((((s - 2) * (m * (m - 1))) % 3 + (2 * m) % 3) % 3) :=
          Nat.add_mod _ _ _
      _ = (((m * (m - 1)) % 3 + (2 * m) % 3) % 3) := by rw [hmul_eq]
      _ = (m * (m - 1) + 2 * m) % 3 :=
          (Nat.add_mod _ _ _).symm
      _ = (m ^ 2 + m) % 3 := by rw [hX]
  rw [heq]
  exact hmem

private theorem polygonal_mod3_ne2_of_mod0 (s m : ℕ) (hs3 : s % 3 = 0) (hs : 3 ≤ s) :
    Nat.polygonalNumber s m % 3 ≠ 2 := by
  have hmem := two_mul_polygonal_mod3 s m hs3 hs
  have hmul := Nat.mul_mod 2 (Nat.polygonalNumber s m) 3
  have h2mod : (2 : ℕ) % 3 = 2 := by decide
  rw [h2mod] at hmul
  omega

private theorem mod12_to_mod4 (s : ℕ) (h : s % 12 = 0 ∨ s % 12 = 4) : s % 4 = 0 := by
  rcases h with h | h <;> omega

private theorem mod12_eq0_to_mod3 (s : ℕ) (h : s % 12 = 0) : s % 3 = 0 := by omega

private theorem mod12_eq4_to_mod3 (s : ℕ) (h : s % 12 = 4) : s % 3 = 1 := by omega

private theorem not_three_dvd_of_mod12 (n q P : ℕ) (hn : n % 12 = 11)
    (heq : n = q + P) (hP : P % 3 ≠ 2) : ¬ 3 ∣ q := by
  omega

private theorem not_four_dvd_of_mod12 (n q P : ℕ) (hn : n % 12 = 11)
    (heq : n = q + P) (hP : P % 4 = 0 ∨ P % 4 = 1) : ¬ 4 ∣ q := by
  rcases hP with hP | hP <;> omega

private theorem mul_ge_of_one_le (s m : ℕ) (hs : 3 ≤ s) (hm : 13 ≤ m) :
    13 ≤ (s - 2) * m := by
  have hs2 : 1 ≤ s - 2 := by omega
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hs2
  have hge : m ≤ (s - 2) * m := by
    rw [hk, Nat.add_mul, Nat.one_mul]
    exact Nat.le_add_right _ _
  omega

private theorem gap_ge (s m : ℕ) (hs : 3 ≤ s) (hm : 13 ≤ m) :
    Nat.polygonalNumber s m + 2 + 13 ≤ Nat.polygonalNumber s (m + 1) + 1 := by
  have hsucc := polygonal_succ s m
  have hge := mul_ge_of_one_le s m hs hm
  omega

private theorem exists_exception_above (N s : ℕ) (hs : 3 ≤ s)
    (hs12 : s % 12 = 0 ∨ s % 12 = 4) :
    ∃ n : ℕ, N < n ∧ 0 < n ∧
      ¬ ∃ q m : ℕ, IsPracticalNumber q ∧ n = q + Nat.polygonalNumber s m := by
  have hs4 : s % 4 = 0 := mod12_to_mod4 s hs12
  have hs3_ne2 : ∀ m : ℕ, Nat.polygonalNumber s m % 3 ≠ 2 := by
    intro m
    rcases hs12 with h12 | h12
    · exact polygonal_mod3_ne2_of_mod0 s m (mod12_eq0_to_mod3 s h12) hs
    · exact polygonal_mod3_ne2_of_mod1 s m (mod12_eq4_to_mod3 s h12) hs
  have hs4_mem : ∀ m : ℕ, Nat.polygonalNumber s m % 4 = 0 ∨
      Nat.polygonalNumber s m % 4 = 1 := fun m => polygonal_mod4_mem s m hs4 hs
  let m := N + 14
  have hm13 : 13 ≤ m := by omega
  have hgap := gap_ge s m hs hm13
  have hPm_ge : m ≤ Nat.polygonalNumber s m := Nat.le_polygonalNumber s m
  let A := Nat.polygonalNumber s m + 2
  let B := Nat.polygonalNumber s (m + 1) + 1
  have hAB : A + 13 ≤ B := hgap
  let t := A + 1
  have htmod_lt : t % 12 < 12 := Nat.mod_lt _ (by decide)
  let n := t + (11 - t % 12)
  have hn_gt_A : A < n := by omega
  have hn_lt_B : n < B := by omega
  have hnmod : n % 12 = 11 := by omega
  have hn_pos : 0 < n := by omega
  have hn_gt_N : N < n := by omega
  refine ⟨n, hn_gt_N, hn_pos, ?_⟩
  rintro ⟨q, k, hq, heq⟩
  have hP3 : Nat.polygonalNumber s k % 3 ≠ 2 := hs3_ne2 k
  have hP4 := hs4_mem k
  have h3 : ¬ 3 ∣ q := not_three_dvd_of_mod12 n q _ hnmod heq hP3
  have h4 : ¬ 4 ∣ q := not_four_dvd_of_mod12 n q _ hnmod heq hP4
  have hq12 := isPracticalNumber_eq_one_or_two q hq h3 h4
  have htri : k ≤ m ∨ m + 1 ≤ k := by omega
  rcases hq12 with rfl | rfl
  · have heq1 : n = Nat.polygonalNumber s k + 1 := by omega
    rcases htri with hkm | hkm
    · have hle := Nat.polygonalNumber_mono s hkm
      omega
    · have hle := Nat.polygonalNumber_mono s hkm
      omega
  · have heq2 : n = Nat.polygonalNumber s k + 2 := by omega
    rcases htri with hkm | hkm
    · have hle := Nat.polygonalNumber_mono s hkm
      omega
    · have hle := Nat.polygonalNumber_mono s hkm
      omega

private theorem infinite_exceptions (s : ℕ) (hs : 3 ≤ s)
    (hs12 : s % 12 = 0 ∨ s % 12 = 4) :
    {n : ℕ | 0 < n ∧ ¬ ∃ q m : ℕ, IsPracticalNumber q ∧
      n = q + Nat.polygonalNumber s m}.Infinite := by
  by_contra hfin
  have hfinite : {n : ℕ | 0 < n ∧ ¬ ∃ q m : ℕ, IsPracticalNumber q ∧
      n = q + Nat.polygonalNumber s m}.Finite :=
    Set.not_infinite.mp hfin
  have hbdd := hfinite.bddAbove
  obtain ⟨N, hN⟩ := hbdd
  obtain ⟨n, hn_gt, hn_pos, hn_not⟩ := exists_exception_above N s hs hs12
  have hn_mem : n ∈ {n : ℕ | 0 < n ∧ ¬ ∃ q m : ℕ, IsPracticalNumber q ∧
      n = q + Nat.polygonalNumber s m} := ⟨hn_pos, hn_not⟩
  have hle : n ≤ N := hN hn_mem
  omega

private theorem odd_not_practical (n : ℕ) (hodd : Odd n) (hgt : 1 < n) :
    ¬ IsPracticalNumber n := by
  obtain ⟨k, rfl⟩ := hodd
  have hk : 1 ≤ k := by omega
  intro h
  obtain ⟨_, hrep⟩ := h
  have h2le : 2 ≤ 2 * k + 1 := by omega
  obtain ⟨s, hs, hsum⟩ := hrep 2 (by decide) h2le
  have hsub : s ⊆ {1} := by
    intro d hd
    have hdvd := Nat.dvd_of_mem_divisors (hs hd)
    have hle : d ≤ 2 := hsum ▸ Finset.single_le_sum (fun i _ ↦ Nat.zero_le i) hd
    have hpos := Nat.pos_of_mem_divisors (hs hd)
    have hd12 : d = 1 ∨ d = 2 := by omega
    have h2ndvd : ¬ 2 ∣ (2 * k + 1) := by omega
    rcases hd12 with rfl | rfl
    · simp
    · exfalso
      exact h2ndvd hdvd
  have hle := Finset.sum_le_sum_of_subset (f := fun d : ℕ ↦ d) hsub
  simp [hsum] at hle

private theorem two_mul_prime_not_practical (p : ℕ) (hp : p.Prime) (h5 : 5 ≤ p) :
    ¬ IsPracticalNumber (2 * p) := by
  intro h
  obtain ⟨_, hrep⟩ := h
  have h4le : 4 ≤ 2 * p := by omega
  obtain ⟨s, hs, hsum⟩ := hrep 4 (by decide) h4le
  have h3ndvd : ¬ 3 ∣ (2 * p) := by
    intro hdvd
    have hp3 : Nat.Prime 3 := by decide
    have h := (hp3.dvd_mul).mp hdvd
    rcases h with h | h
    · have h32 : ¬ (3 ∣ 2) := by decide
      exact h32 h
    · have heq := (Nat.prime_dvd_prime_iff_eq hp3 hp).mp h
      omega
  have h4ndvd : ¬ 4 ∣ (2 * p) := by
    intro hdvd
    obtain ⟨k, hk⟩ := hdvd
    have hp2 : Nat.Prime 2 := by decide
    have h2dvd : 2 ∣ p := ⟨k, by omega⟩
    have heq := (Nat.prime_dvd_prime_iff_eq hp2 hp).mp h2dvd
    omega
  have hsub : s ⊆ {1, 2} := by
    intro d hd
    have hdvd := Nat.dvd_of_mem_divisors (hs hd)
    have hle : d ≤ 4 := hsum ▸ Finset.single_le_sum (fun i _ ↦ Nat.zero_le i) hd
    have hpos := Nat.pos_of_mem_divisors (hs hd)
    have hd3 : d ≠ 3 := fun e => h3ndvd (e ▸ hdvd)
    have hd4 : d ≠ 4 := fun e => h4ndvd (e ▸ hdvd)
    simp only [Finset.mem_insert, Finset.mem_singleton]
    omega
  have hle := Finset.sum_le_sum_of_subset (f := fun d : ℕ ↦ d) hsub
  simp [hsum] at hle

private theorem choose_two_ge_one (x : ℕ) (hx : 2 ≤ x) : 1 ≤ x.choose 2 :=
  Nat.choose_pos hx

private theorem polygonal_ge_self_of_ge_two (t x : ℕ) (ht : 2 ≤ t) (hx : 2 ≤ x) :
    t ≤ Nat.polygonalNumber t x := by
  have hC : 1 ≤ x.choose 2 := choose_two_ge_one x hx
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hC
  have hmul : t - 2 ≤ (t - 2) * (1 + k) := by
    rw [Nat.mul_add, Nat.mul_one]
    exact Nat.le_add_right _ _
  have hP : (t - 2) + 2 ≤ (t - 2) * (1 + k) + x := Nat.add_le_add hmul hx
  have ht2 : (t - 2) + 2 = t := Nat.sub_add_cancel ht
  rw [ht2] at hP
  have hCeq : x.choose 2 = 1 + k := hk
  simp only [Nat.polygonalNumber, hCeq]
  exact hP

private theorem exists_finset_primes_ge5 (M : ℕ) :
    ∃ P : Finset ℕ, M ≤ P.card ∧ ∀ p ∈ P, p.Prime ∧ 5 ≤ p := by
  obtain ⟨F, hFsub, hFcard⟩ :=
    Nat.infinite_setOfPred_prime.exists_subset_card_eq (M + 2)
  have hprime : ∀ p ∈ F, p.Prime := fun p hp => hFsub (Finset.mem_coe.mpr hp)
  have hcard_eq := Finset.card_filter_add_card_filter_not (s := F) (fun p => 5 ≤ p)
  have hsmall_subset : F.filter (fun p => ¬ 5 ≤ p) ⊆ ({2, 3} : Finset ℕ) := by
    intro p hp
    simp only [Finset.mem_filter] at hp
    obtain ⟨hpF, hp5⟩ := hp
    have hpr := hprime p hpF
    have h2le := hpr.two_le
    have hp4 : p ≠ 4 := by
      intro e
      rw [e] at hpr
      have h4 : ¬ Nat.Prime 4 := by decide
      exact h4 hpr
    simp only [Finset.mem_insert, Finset.mem_singleton]
    omega
  have hsmall_le : (F.filter (fun p => ¬ 5 ≤ p)).card ≤ 2 := by
    have hle := Finset.card_le_card hsmall_subset
    have h23 : (({2, 3} : Finset ℕ)).card = 2 := by decide
    omega
  have hPcard : M ≤ (F.filter (fun p => 5 ≤ p)).card := by omega
  refine ⟨F.filter (fun p => 5 ≤ p), hPcard, fun p hp => ?_⟩
  simp only [Finset.mem_filter] at hp
  exact ⟨hprime p hp.1, hp.2⟩

private theorem image_card_ge (P : Finset ℕ) (M : ℕ) (hM : M ≤ P.card) :
    M ≤ (P.image (fun p => 2 * p + 1)).card := by
  have hinj : Function.Injective (fun p : ℕ => 2 * p + 1) := by
    intro a b hab
    simp only at hab
    omega
  have hcard := Finset.card_image_of_injective P hinj
  omega

private theorem exists_many_exceptions (M : ℕ) :
    ∃ S : ℕ, ∀ t ≥ S, ∃ F : Finset ℕ, M ≤ F.card ∧ ∀ n ∈ F, 0 < n ∧
      ¬ ∃ q x y : ℕ, IsPracticalNumber q ∧
        n = q + Nat.polygonalNumber t x + Nat.polygonalNumber t y := by
  obtain ⟨P, hPcard, hPmem⟩ := exists_finset_primes_ge5 M
  let F0 := P.image (fun p => 2 * p + 1)
  have hF0card : M ≤ F0.card := image_card_ge P M hPcard
  let S := 2 * (P.sup id) + 2
  refine ⟨S, fun t ht => ⟨F0, hF0card, fun n hn => ?_⟩⟩
  simp only [F0, Finset.mem_image] at hn
  obtain ⟨p, hpP, rfl⟩ := hn
  obtain ⟨hprime, h5⟩ := hPmem p hpP
  have hple : p ≤ P.sup id := Finset.le_sup (f := id) hpP
  have hn_lt_t : 2 * p + 1 < t := by omega
  have ht2 : 2 ≤ t := by omega
  have hn_pos : 0 < 2 * p + 1 := by omega
  refine ⟨hn_pos, ?_⟩
  rintro ⟨q, x, y, hq, heq⟩
  have hqpos := hq.1
  have hx_lt : Nat.polygonalNumber t x < t := by omega
  have hy_lt : Nat.polygonalNumber t y < t := by omega
  have hx_le1 : x ≤ 1 := by
    by_contra hcon
    have hx2 : 2 ≤ x := by omega
    have hge := polygonal_ge_self_of_ge_two t x ht2 hx2
    omega
  have hy_le1 : y ≤ 1 := by
    by_contra hcon
    have hy2 : 2 ≤ y := by omega
    have hge := polygonal_ge_self_of_ge_two t y ht2 hy2
    omega
  have hx01 : x = 0 ∨ x = 1 := by omega
  have hy01 : y = 0 ∨ y = 1 := by omega
  rcases hx01 with rfl | rfl <;> rcases hy01 with rfl | rfl <;>
    simp only [Nat.polygonalNumber_zero, Nat.polygonalNumber_one] at heq
  · have hqn : q = 2 * p + 1 := by omega
    rw [hqn] at hq
    exact odd_not_practical _ ⟨p, rfl⟩ (by omega) hq
  · have hqn : q = 2 * p := by omega
    rw [hqn] at hq
    exact two_mul_prime_not_practical p hprime h5 hq
  · have hqn : q = 2 * p := by omega
    rw [hqn] at hq
    exact two_mul_prime_not_practical p hprime h5 hq
  · have hqn : q + 2 = 2 * p + 1 := by omega
    have hqeq : q = 2 * p - 1 := by omega
    have hodd : Odd q := ⟨p - 1, by omega⟩
    have hgt : 1 < q := by omega
    exact odd_not_practical q hodd hgt hq

@[expose] public section

/-- **Exceptions to sums of a practical number and polygonal numbers.** (a) Let $s \ge 3$ with
$s \equiv 0$ or $s \equiv 4 \pmod{12}$. Then there are infinitely many positive integers $n$ that
cannot be written as $n = q + p_s(m)$ with $q$ a practical number and $m \ge 0$ an integer, where
$p_s(m)$ is the $m$-th $s$-gonal number. (b) For every natural number $M$ there is a natural
number $S$ such that for every $t \ge S$ there are at least $M$ positive integers $n$ that cannot
be written as $n = q + p_t(x) + p_t(y)$ with $q$ a practical number and integers $x, y \ge 0$.

Source: Sai Teja Somu and Duc Van Khanh Tran, *On Sums of Practical Numbers and Polygonal
Numbers*, Journal of Integer Sequences 27 (2024), Article 24.5.1, Proposition 12
(arXiv Proposition 4.7; `jis-2024-24.5.1-prop-12`). -/
public theorem practical_add_polygonal_exceptions (s : ℕ) :
    ((3 ≤ s ∧ (s % 12 = 0 ∨ s % 12 = 4)) →
      {n : ℕ | 0 < n ∧
        ¬ ∃ q m : ℕ, IsPracticalNumber q ∧ n = q + Nat.polygonalNumber s m}.Infinite) ∧
    ∀ M : ℕ, ∃ S : ℕ, ∀ t ≥ S, ∃ F : Finset ℕ, M ≤ F.card ∧ ∀ n ∈ F, 0 < n ∧
      ¬ ∃ q x y : ℕ, IsPracticalNumber q ∧ n = q + Nat.polygonalNumber t x + Nat.polygonalNumber t y
    := by
  constructor
  · intro h
    obtain ⟨hs, hs12⟩ := h
    exact infinite_exceptions s hs hs12
  · exact exists_many_exceptions

end

end MetaMathlibExt
