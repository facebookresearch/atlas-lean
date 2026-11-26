/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Nat.Nth
public import Mathlib.Data.Nat.PrimeFin
public import Mathlib.Data.Nat.ModEq
public import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Hybrid bounds for prime divisors

We prove simultaneous bounds for products of initial primes in congruence classes
associated with an ordered list of distinct prime factors of an exponent.

Source: Gustav Kjærbye Bagger, *Hybrid Bounds for Prime Divisors*, INTEGERS 26 (2026),
Article A95, Theorem 1.
-/

namespace MetaMathlibExt

open Finset

private theorem nth_mem_of_finset (P : ℕ → Prop) (s : Finset ℕ)
    (hs : ∀ q ∈ s, P q) {i : ℕ} (hi : i < s.card) : P (Nat.nth P i) := by
  classical
  apply Nat.nth_mem
  intro hf
  exact hi.trans_le (card_le_card fun q hq => hf.mem_toFinset.mpr (hs q hq))

private theorem prod_nth_le (P : ℕ → Prop) (s : Finset ℕ)
    (hs : ∀ q ∈ s, P q) : ∏ i ∈ range s.card, Nat.nth P i ≤ ∏ q ∈ s, q := by
  classical
  induction s using Finset.induction_on_max with
  | empty => simp
  | insert q s hlt ih =>
    have hq := hs q (mem_insert_self q s)
    have hs' : ∀ r ∈ s, P r := forall_of_forall_insert hs
    have hcount : s.card ≤ Nat.count P q := by
      rw [Nat.count_eq_card_filter_range]
      exact card_le_card fun r hr => mem_filter.mpr ⟨mem_range.mpr (hlt r hr), hs' r hr⟩
    have hnth := Nat.nth_le_nth' hcount (fun hf => Nat.count_lt_card hf hq)
    rw [Nat.nth_count hq] at hnth
    have hqs : q ∉ s := fun h => (hlt q h).false
    rw [card_insert_of_notMem hqs, prod_range_succ, prod_insert hqs, mul_comm q]
    exact Nat.mul_le_mul (ih hs') hnth

private noncomputable def last_index (m : ℕ) (p : ℕ → ℕ) (ρ : ℕ) : ℕ :=
  ((Icc 1 m).filter (fun s => Nat.ModEq (p s) ρ 1)).sup id

private theorem last_index_le (m : ℕ) (p : ℕ → ℕ) (ρ : ℕ) : last_index m p ρ ≤ m := by
  classical
  exact Finset.sup_le fun s hs => (mem_Icc.mp (mem_filter.mp hs).1).2

private theorem last_index_class (m : ℕ) (p : ℕ → ℕ) (ρ : ℕ) :
    (last_index m p ρ = 0 ∨ Nat.ModEq (p (last_index m p ρ)) ρ 1) ∧
      ∀ s ∈ Ioc (last_index m p ρ) m, ¬ Nat.ModEq (p s) ρ 1 := by
  classical
  let v := (Icc 1 m).filter (fun s => Nat.ModEq (p s) ρ 1)
  constructor
  · by_cases hv : v.Nonempty
    · obtain ⟨s, hs, heq⟩ := v.sup_mem_of_nonempty (f := id) hv
      have h : Nat.ModEq (p (v.sup id)) ρ 1 := by
        simpa only [← heq, id_eq] using (mem_filter.mp hs).2
      exact Or.inr h
    · left
      simp [last_index, v, not_nonempty_iff_eq_empty.mp hv]
  · intro s hs hcong
    have hmem : s ∈ v := mem_filter.mpr ⟨mem_Icc.mpr
      ⟨by have := (mem_Ioc.mp hs).1; omega, (mem_Ioc.mp hs).2⟩, hcong⟩
    exact (not_le_of_gt (mem_Ioc.mp hs).1) (le_sup (f := id) hmem)

private theorem dvd_prefix_exponent (m t d : ℕ) (p a : ℕ → ℕ)
    (hp : ∀ i ∈ Icc 1 m, (p i).Prime) (ht : t ≤ m)
    (hd : d ∣ ∏ i ∈ Icc 1 m, p i ^ a i)
    (hc : ∀ s ∈ Ioc t m, ¬ p s ∣ d) : d ∣ ∏ i ∈ Icc 1 t, p i ^ a i := by
  induction m with
  | zero =>
    have htz : t = 0 := Nat.eq_zero_of_le_zero ht
    simpa only [htz] using hd
  | succ m ih =>
    by_cases htm : t ≤ m
    · have hlast : m + 1 ∈ Icc 1 (m + 1) := mem_Icc.mpr ⟨Nat.succ_pos m, le_rfl⟩
      have hcop := (hp _ hlast).coprime_pow_of_not_dvd (m := a (m + 1))
        (hc _ (mem_Ioc.mpr ⟨by omega, le_rfl⟩))
      rw [prod_Icc_succ_top (Nat.succ_pos m)] at hd
      exact ih (fun i hi => hp i (Icc_subset_Icc_right (Nat.le_succ m) hi)) htm
        (hcop.dvd_of_dvd_mul_right hd)
        (fun s hs => hc s (mem_Ioc.mpr ⟨(mem_Ioc.mp hs).1,
          (mem_Ioc.mp hs).2.trans (Nat.le_succ m)⟩))
    · have hteq : t = m + 1 := by omega
      simpa only [hteq] using hd

private theorem prime_dvd_prefix (m t : ℕ) (p a : ℕ → ℕ)
    (hp : ∀ i ∈ Icc 1 m, (p i).Prime) (ht : t ≤ m) {x ρ : ℕ}
    (hx : 1 < x) (hρ : ρ.Prime)
    (hdiv : ρ ∣ x ^ (∏ i ∈ Icc 1 m, p i ^ a i) - 1)
    (hc : ∀ s ∈ Ioc t m, ¬ Nat.ModEq (p s) ρ 1) :
    ρ ∣ x ^ (∏ i ∈ Icc 1 t, p i ^ a i) - 1 := by
  have : Fact ρ.Prime := ⟨hρ⟩
  have hN : (∏ i ∈ Icc 1 m, p i ^ a i) ≠ 0 :=
    prod_ne_zero_iff.mpr fun i hi => pow_ne_zero _ (hp i hi).ne_zero
  have hpow : 1 < x ^ (∏ i ∈ Icc 1 m, p i ^ a i) := one_lt_pow₀ hx hN
  have hz : (x : ZMod ρ) ^ (∏ i ∈ Icc 1 m, p i ^ a i) = 1 := by
    simpa only [Nat.cast_pow, Nat.cast_one] using
      (ZMod.natCast_eq_natCast_iff _ _ ρ).mpr
        ((Nat.modEq_iff_dvd' hpow.le).mpr hdiv).symm
  have hxz : (x : ZMod ρ) ≠ 0 := by
    intro hzero
    rw [hzero, zero_pow hN] at hz
    exact zero_ne_one hz
  have hd := orderOf_dvd_of_pow_eq_one hz
  have hord := ZMod.orderOf_dvd_card_sub_one hxz
  have hdt := dvd_prefix_exponent m t (orderOf (x : ZMod ρ)) p a hp ht hd
    (fun s hs hsd => hc s hs
      ((Nat.modEq_iff_dvd' hρ.one_le).mpr (hsd.trans hord)).symm)
  have hzt := orderOf_dvd_iff_pow_eq_one.mp hdt
  apply (Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ (by omega))).mp
  exact ((ZMod.natCast_eq_natCast_iff _ _ ρ).mp
    (by simpa only [Nat.cast_pow, Nat.cast_one] using hzt)).symm

/-- The hybrid bound. Let `n = ∏_{i=1}^m p_i^{a_i}` with distinct primes `p_i` (in any order),
`x > 1`, and `ω_n = ω(x^n - 1)`. With `p_0 := 1`, let
`Π^j = {ρ prime : ρ ≡ 1 (mod p_j), ρ ≢ 1 (mod p_s) for j < s ≤ m}` and `r_{i,j}` its `i`-th
element (`Nat.nth`, `0`-indexed here). The source's
`x ≥ min_{k_0 + ⋯ + k_m = ω_n} max_{0 ≤ t ≤ m} (1 + ∏_{j ≤ t} ∏_{i ≤ k_j} r_{i,j})^{T(t)}` with
`T(t) = ∏_{s=1}^t p_s^{-a_s}` is stated equivalently, after raising to the power
`∏_{s ≤ t} p_s^{a_s}`, as the existence of a composition `k` meeting every bound. The parts `k_j`
range over `ℕ` (the source writes `k_i ∈ ℤ⁺`; with positive parts the claim fails for
`n = 3`, `x = 2`, where `x^3 - 1 = 7` and `ω_n = 1` admits no positive composition into two
parts). The source's factors are all primes, and since `Nat.nth` returns `0` past the end of
a finite set, the statement requires every factor to be a genuine (positive) element of its
prime class.

Source: Gustav Kjærbye Bagger, *Hybrid Bounds for Prime Divisors*, INTEGERS 26 (2026),
Article A95, Theorem 1 (`integers-2026-A95-thm-1`). -/
public theorem hybrid_bound_prime_divisors (m : ℕ) (p a : ℕ → ℕ)
    (hp : ∀ i ∈ Finset.Icc 1 m, (p i).Prime) (hinj : Set.InjOn p (Finset.Icc 1 m))
    (ha : ∀ i ∈ Finset.Icc 1 m, 0 < a i) {x : ℕ} (hx : 1 < x) :
    ∃ k : ℕ → ℕ,
      ∑ j ∈ Finset.range (m + 1), k j =
          (x ^ (∏ i ∈ Finset.Icc 1 m, p i ^ a i) - 1).primeFactors.card ∧
        (∀ j ≤ m, ∀ i < k j, 0 < Nat.nth (fun ρ => ρ.Prime ∧
          (j = 0 ∨ Nat.ModEq (p j) ρ 1) ∧
            ∀ s ∈ Finset.Ioc j m, ¬ Nat.ModEq (p s) ρ 1) i) ∧
        ∀ t ≤ m,
          1 + ∏ j ∈ Finset.range (t + 1), ∏ i ∈ Finset.range (k j),
              Nat.nth (fun ρ => ρ.Prime ∧ (j = 0 ∨ Nat.ModEq (p j) ρ 1) ∧
                ∀ s ∈ Finset.Ioc j m, ¬ Nat.ModEq (p s) ρ 1) i ≤
            x ^ ∏ s ∈ Finset.Icc 1 t, p s ^ a s := by
  classical
  have _ := hinj
  have _ := ha
  let S := (x ^ (∏ i ∈ Icc 1 m, p i ^ a i) - 1).primeFactors
  let f := last_index m p
  let B := fun j => S.filter (fun ρ => f ρ = j)
  let P := fun j ρ => ρ.Prime ∧ (j = 0 ∨ Nat.ModEq (p j) ρ 1) ∧
    ∀ s ∈ Ioc j m, ¬ Nat.ModEq (p s) ρ 1
  have hB : ∀ j, ∀ ρ ∈ B j, P j ρ := by
    intro j ρ hρ
    obtain ⟨hρS, hρj⟩ := mem_filter.mp hρ
    have hclass := last_index_class m p ρ
    rw [← hρj]
    exact ⟨Nat.prime_of_mem_primeFactors hρS, hclass⟩
  refine ⟨fun j => (B j).card, ?_, ?_, ?_⟩
  · exact (card_eq_sum_card_fiberwise (f := f) (s := S) (t := range (m + 1))
      (fun ρ _ => mem_range.mpr (Nat.lt_succ_of_le (last_index_le m p ρ)))).symm
  · intro j hj i hi
    exact (nth_mem_of_finset (P j) (B j) (hB j) hi).1.pos
  · intro t ht
    have hN : (∏ s ∈ Icc 1 t, p s ^ a s) ≠ 0 :=
      prod_ne_zero_iff.mpr fun s hs => pow_ne_zero _
        (hp s (Icc_subset_Icc_right ht hs)).ne_zero
    have hpow : 1 < x ^ (∏ s ∈ Icc 1 t, p s ^ a s) := one_lt_pow₀ hx hN
    have hsub : S.filter (fun ρ => f ρ ∈ range (t + 1)) ⊆
        (x ^ (∏ s ∈ Icc 1 t, p s ^ a s) - 1).primeFactors := by
      intro ρ hρ
      obtain ⟨hρS, hρt⟩ := mem_filter.mp hρ
      have hρp := Nat.prime_of_mem_primeFactors hρS
      refine Nat.mem_primeFactors.mpr ⟨hρp, ?_, by omega⟩
      apply prime_dvd_prefix m t p a hp ht hx hρp (Nat.dvd_of_mem_primeFactors hρS)
      intro s hs
      exact (last_index_class m p ρ).2 s (mem_Ioc.mpr
        ⟨(Nat.le_of_lt_succ (mem_range.mp hρt)).trans_lt (mem_Ioc.mp hs).1,
          (mem_Ioc.mp hs).2⟩)
    have hle : (∏ j ∈ range (t + 1), ∏ i ∈ range (B j).card, Nat.nth (P j) i) ≤
        x ^ (∏ s ∈ Icc 1 t, p s ^ a s) - 1 := by
      calc
        _ ≤ ∏ j ∈ range (t + 1), ∏ ρ ∈ B j, ρ :=
          prod_le_prod fun j _ => prod_nth_le (P j) (B j) (hB j)
        _ = ∏ ρ ∈ S.filter (fun ρ => f ρ ∈ range (t + 1)), ρ :=
          prod_fiberwise_eq_prod_filter S (range (t + 1)) f id
        _ ≤ x ^ (∏ s ∈ Icc 1 t, p s ^ a s) - 1 :=
          Nat.le_of_dvd (by omega) ((prod_dvd_prod_of_subset _ _ id hsub).trans
            (Nat.prod_primeFactors_dvd _))
    change 1 + (∏ j ∈ range (t + 1), ∏ i ∈ range (B j).card, Nat.nth (P j) i) ≤ _
    omega

end MetaMathlibExt
