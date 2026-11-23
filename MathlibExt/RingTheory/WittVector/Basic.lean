/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_WittVector_coeff_eq_coeff_of_forall_ghostComponent_eq.lean`,
`P2M/Sol/S_WittVector_coeff_eq_coeff_of_forall_ghostComponent_eq.lean`,
`Theorems/Thm_WittVector_exists_forall_ghostComponent_eq_of_sub_frobeniusLift_mem.lean`,
`P2M/Sol/S_WittVector_exists_forall_ghostComponent_eq_of_sub_frobeniusLift_mem.lean`,
`Theorems/Thm_WittVector_ringHom_map_frobenius_of_finite.lean`,
`P2M/Sol/S_WittVector_ringHom_map_frobenius_of_finite.lean`,
`Theorems/Thm_WittVector_coeff_mem_span_of_ghostComponent_mem_span_pow_of_isReduced.lean` and
`P2M/Sol/S_WittVector_coeff_mem_span_of_ghostComponent_mem_span_pow_of_isReduced.lean`
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

public import Mathlib.RingTheory.WittVector.Compare
public import Mathlib.RingTheory.WittVector.Frobenius
public import Mathlib.RingTheory.WittVector.Verschiebung
public import Mathlib.RingTheory.WittVector.Teichmuller
public import Mathlib.RingTheory.WittVector.Identities
public import Mathlib.RingTheory.WittVector.Domain
public import Mathlib.NumberTheory.Basic
public import Mathlib.Tactic.Ring

/-!
# Witt vectors: ghost components, Frobenius, and coefficient bounds

Ghost components determine Witt vector coefficients when `p` is a
non-zero-divisor; compatible ghost data with a Frobenius lift is realized
by a Witt vector; ring homomorphisms out of Witt vectors over a finite
field commute with Frobenius; and coefficients of a Witt vector whose
ghost component is highly `p`-divisible lie in `(p)` when the reduction
mod `p` is reduced.
-/

@[expose] public section

universe u v

namespace WittGhostAux

variable {R : Type*} [CommRing R] {p : ℕ} [Fact p.Prime]

private theorem ghost_eq_sum (k : ℕ) (x : WittVector p R) :
    WittVector.ghostComponent k x =
      ∑ i ∈ Finset.range (k + 1), (p : R) ^ i * x.coeff i ^ p ^ (k - i) := by
  rw [WittVector.ghostComponent_apply, aeval_wittPolynomial]

omit [Fact p.Prime] in
private theorem pow_sub_pow_mem {a b : R} (h : a - b ∈ Ideal.span {(p : R)}) (m : ℕ) :
    a ^ p ^ m - b ^ p ^ m ∈ Ideal.span {(p : R) ^ (m + 1)} := by
  have h' := dvd_sub_pow_of_dvd_sub (Ideal.mem_span_singleton.1 h) m
  rw [Ideal.mem_span_singleton]
  exact_mod_cast h'

private theorem ghost_succ_eq (k : ℕ) (x : WittVector p R) :
    WittVector.ghostComponent (k + 1) x =
      ∑ i ∈ Finset.range (k + 1), (p : R) ^ i * x.coeff i ^ p ^ (k + 1 - i) +
        (p : R) ^ (k + 1) * x.coeff (k + 1) := by
  rw [ghost_eq_sum, Finset.sum_range_succ, Nat.sub_self, pow_zero, pow_one]

private theorem ghost_succ_sub_mem (σ : R →+* R)
    (hσ : ∀ a : R, σ a - a ^ p ∈ Ideal.span {(p : R)})
    (x : WittVector p R) (k : ℕ) :
    WittVector.ghostComponent (k + 1) x - σ (WittVector.ghostComponent k x) ∈
      Ideal.span {(p : R) ^ (k + 1)} := by
  have hterm : ∀ i ∈ Finset.range (k + 1),
      (p : R) ^ i * x.coeff i ^ p ^ (k + 1 - i) -
        σ ((p : R) ^ i * x.coeff i ^ p ^ (k - i)) ∈
        Ideal.span {(p : R) ^ (k + 1)} := by
    intro i hi
    rw [Finset.mem_range] at hi
    rw [map_mul, map_pow, map_natCast, map_pow, ← mul_sub,
      show k + 1 - i = k - i + 1 by omega, pow_succ' (p : ℕ) (k - i), pow_mul]
    have hd := pow_sub_pow_mem (p := p) (a := x.coeff i ^ p) (b := σ (x.coeff i))
      (by rw [← neg_sub]; exact (Ideal.neg_mem_iff _).2 (hσ _)) (k - i)
    rw [Ideal.mem_span_singleton] at hd ⊢
    have hpk : (p : R) ^ (k + 1) = (p : R) ^ i * (p : R) ^ (k - i + 1) := by
      rw [← pow_add]; congr 1; omega
    rw [hpk]
    exact mul_dvd_mul_left _ hd
  rw [ghost_succ_eq, ghost_eq_sum, map_sum, add_sub_right_comm, ← Finset.sum_sub_distrib]
  exact Ideal.add_mem _ (Ideal.sum_mem _ hterm)
    (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))

private theorem exists_ghost_eq (σ : R →+* R)
    (hσ : ∀ a : R, σ a - a ^ p ∈ Ideal.span {(p : R)})
    (n : ℕ) (g : ℕ → R)
    (hg : ∀ k : ℕ, k + 1 < n → g (k + 1) - σ (g k) ∈ Ideal.span {(p : R) ^ (k + 1)}) :
    ∃ x : WittVector p R, ∀ k < n, WittVector.ghostComponent k x = g k := by
  induction n with
  | zero => exact ⟨0, fun k hk => absurd hk (Nat.not_lt_zero _)⟩
  | succ n ih =>
    obtain ⟨x, hx⟩ := ih (fun k hk => hg k (by omega))
    have hdef : g n - ∑ i ∈ Finset.range n, (p : R) ^ i * x.coeff i ^ p ^ (n - i) ∈
        Ideal.span {(p : R) ^ n} := by
      cases n with
      | zero => simp
      | succ k =>
        have h1 := hg k (by omega)
        have h3 := ghost_succ_sub_mem σ hσ x k
        rw [hx k (by omega)] at h3
        have key : g (k + 1) -
            ∑ i ∈ Finset.range (k + 1), (p : R) ^ i * x.coeff i ^ p ^ (k + 1 - i) =
            (g (k + 1) - σ (g k)) - (WittVector.ghostComponent (k + 1) x - σ (g k)) +
              (p : R) ^ (k + 1) * x.coeff (k + 1) := by
          rw [ghost_succ_eq]; ring
        rw [key]
        exact Ideal.add_mem _ (Ideal.sub_mem _ h1 h3)
          (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hdef
    refine ⟨WittVector.mk p (fun i => if i = n then c else x.coeff i), fun k hk => ?_⟩
    by_cases hkn : k < n
    · rw [← hx k hkn, ghost_eq_sum, ghost_eq_sum]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [Finset.mem_range] at hi
      simp only [WittVector.coeff_mk]
      rw [ite_eq_right (show i ≠ n by omega)]
    · have hkn' : k = n := by omega
      rw [hkn', ghost_eq_sum, Finset.sum_range_succ, Nat.sub_self, pow_zero, pow_one]
      simp only [WittVector.coeff_mk, ite_true]
      have hS : ∑ i ∈ Finset.range n,
          (p : R) ^ i * (if i = n then c else x.coeff i) ^ p ^ (n - i) =
          ∑ i ∈ Finset.range n, (p : R) ^ i * x.coeff i ^ p ^ (n - i) :=
        Finset.sum_congr rfl fun i hi => by
          rw [ite_eq_right (show i ≠ n from fun h => by
            rw [Finset.mem_range] at hi; omega)]
      rw [hS, mul_comm ((p : R) ^ n) c, hc]
      ring

private theorem coeff_eq_of_ghost_eq (hpR : (p : R) ∈ nonZeroDivisors R) (n : ℕ)
    (x y : WittVector p R)
    (h : ∀ k < n, WittVector.ghostComponent k x = WittVector.ghostComponent k y) :
    ∀ k < n, x.coeff k = y.coeff k := by
  intro k
  refine Nat.strong_induction_on k ?_
  intro k ih hk
  have hk' := h k hk
  rw [ghost_eq_sum, ghost_eq_sum, Finset.sum_range_succ, Finset.sum_range_succ, Nat.sub_self,
    pow_zero, pow_one, pow_one] at hk'
  have hS : ∑ i ∈ Finset.range k, (p : R) ^ i * x.coeff i ^ p ^ (k - i) =
      ∑ i ∈ Finset.range k, (p : R) ^ i * y.coeff i ^ p ^ (k - i) :=
    Finset.sum_congr rfl fun i hi => by
      rw [ih i (Finset.mem_range.1 hi) (lt_trans (Finset.mem_range.1 hi) hk)]
  rw [hS, add_right_inj] at hk'
  exact sub_eq_zero.1
    ((mem_nonZeroDivisors_iff.1 (pow_mem hpR k)).1 _ (by rw [mul_sub, hk', sub_self]))

end WittGhostAux

/-- Ghost components determine Witt vector coefficients when `p` is a
non-zero-divisor. -/
theorem WittVector.coeff_eq_coeff_of_forall_ghostComponent_eq {R : Type u}
    [CommRing R] (p : ℕ) [Fact p.Prime] (hp : (p : R) ∈ nonZeroDivisors R)
    (n : ℕ) (x y : WittVector p R)
    (h : ∀ k < n, WittVector.ghostComponent k x = WittVector.ghostComponent k y) :
    ∀ k < n, x.coeff k = y.coeff k :=
  WittGhostAux.coeff_eq_of_ghost_eq hp n x y h

/-- Compatible ghost data with a Frobenius lift is realized by a Witt
vector. -/
theorem WittVector.exists_forall_ghostComponent_eq_of_sub_frobeniusLift_mem
    {R : Type u} [CommRing R] (p : ℕ) [Fact p.Prime] (σ : R →+* R)
    (hσ : ∀ a : R, σ a - a ^ p ∈ Ideal.span {(p : R)})
    (n : ℕ) (g : ℕ → R)
    (hg : ∀ k : ℕ, k + 1 < n → g (k + 1) - σ (g k) ∈ Ideal.span {(p : R) ^ (k + 1)}) :
    ∃ x : WittVector p R, ∀ k < n, WittVector.ghostComponent k x = g k :=
  WittGhostAux.exists_ghost_eq σ hσ n g hg

namespace WittRigidAux

open WittVector

private theorem eq_zero_of_forall_pow_dvd {p : ℕ} [Fact p.Prime] {R : Type u} [CommRing R]
    [CharP R p] (x : WittVector p R) (h : ∀ N : ℕ, ((p : WittVector p R) ^ N) ∣ x) :
    x = 0 := by
  ext i
  obtain ⟨y, hy⟩ := h (i + 1)
  rw [hy, mul_comm, WittVector.mul_pow_charP_coeff_zero y (Nat.lt_succ_self i),
    WittVector.zero_coeff]

private theorem sub_coeff_zero {p : ℕ} [Fact p.Prime] {R : Type u} [CommRing R] [CharP R p]
    (x y : WittVector p R) : (x - y).coeff 0 = x.coeff 0 - y.coeff 0 := by
  have h := WittVector.add_coeff_zero (x - y) y
  rw [sub_add_cancel] at h
  rw [h, add_sub_cancel_right]

private theorem pow_coeff_zero {p : ℕ} [Fact p.Prime] {R : Type u} [CommRing R] [CharP R p]
    (x : WittVector p R) (n : ℕ) : (x ^ n).coeff 0 = x.coeff 0 ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, WittVector.one_coeff_zero]
  | succ n ih => rw [pow_succ, pow_succ, WittVector.mul_coeff_zero, ih]

private theorem exists_eq_p_mul_of_coeff_zero {p : ℕ} [Fact p.Prime] {R : Type u} [CommRing R]
    [CharP R p] [PerfectRing R p] (y : WittVector p R) (hy : y.coeff 0 = 0) :
    ∃ z : WittVector p R, y = (p : WittVector p R) * z := by
  have hV : y = verschiebung (y.shift 1) := by
    have hthis := WittVector.eq_iterate_verschiebung (x := y) (n := 1) (fun i hi => by
      have : i = 0 := by omega
      subst this; exact hy)
    simpa using hthis
  obtain ⟨z, hz⟩ := (WittVector.frobenius_bijective p R).2 (y.shift 1)
  refine ⟨z, ?_⟩
  rw [hV, ← hz, WittVector.verschiebung_frobenius, mul_comm]

private theorem exists_eq_teichmuller_add {p : ℕ} [Fact p.Prime] {R : Type u} [CommRing R]
    [CharP R p] [PerfectRing R p] (x : WittVector p R) :
    ∃ z : WittVector p R, x = teichmuller p (x.coeff 0) + (p : WittVector p R) * z := by
  obtain ⟨z, hz⟩ := exists_eq_p_mul_of_coeff_zero (x - teichmuller p (x.coeff 0))
    (by rw [sub_coeff_zero, WittVector.teichmuller_coeff_zero, sub_self])
  exact ⟨z, by rw [← hz, add_sub_cancel]⟩

private theorem exists_mem_closure_add_pow_mul {p : ℕ} [Fact p.Prime] {R : Type u} [CommRing R]
    [CharP R p] [PerfectRing R p] (N : ℕ) (x : WittVector p R) :
    ∃ y ∈ Subring.closure (Set.range (teichmuller p : R → WittVector p R)),
      ∃ z : WittVector p R, x = y + (p : WittVector p R) ^ N * z := by
  induction N generalizing x with
  | zero => exact ⟨0, Subring.zero_mem _, x, by simp⟩
  | succ N ih =>
      obtain ⟨x', hx'⟩ := exists_eq_teichmuller_add x
      obtain ⟨y, hy, z, hz⟩ := ih x'
      refine ⟨teichmuller p (x.coeff 0) + (p : WittVector p R) * y, ?_, z, ?_⟩
      · exact Subring.add_mem _ (Subring.subset_closure ⟨_, rfl⟩)
          (Subring.mul_mem _ (natCast_mem _ p) hy)
      · calc x = teichmuller p (x.coeff 0) + (p : WittVector p R) * x' := hx'
          _ = _ := by rw [hz]; ring

private theorem apply_teichmuller_eq {p : ℕ} [Fact p.Prime] {F : Type u} [Field F] [Finite F]
    [CharP F p] {k : Type v} [CommRing k] [CharP k p] [PerfectRing k p]
    (ι : WittVector p F →+* WittVector p k) (z : F) :
    ι (teichmuller p z) = teichmuller p ((ι (teichmuller p z)).coeff 0) := by
  classical
  let _ : Fintype F := Fintype.ofFinite F
  obtain ⟨d, -, hcard⟩ := FiniteField.card F p
  set q : ℕ := Fintype.card F with hq
  set w : WittVector p k := ι (teichmuller p z) with hw
  set w₀ : k := w.coeff 0 with hw₀
  have hwq : w ^ q = w := by
    rw [hw, ← map_pow, ← map_pow, FiniteField.pow_card]
  have hw₀q : w₀ ^ q = w₀ := by rw [hw₀, ← pow_coeff_zero, hwq]
  have hwqn : ∀ n : ℕ, w ^ q ^ n = w := by
    intro n
    induction n with
    | zero => rw [pow_zero, pow_one]
    | succ n ih => rw [pow_succ, pow_mul, ih, hwq]
  have hw₀qn : ∀ n : ℕ, w₀ ^ q ^ n = w₀ := by
    intro n
    induction n with
    | zero => rw [pow_zero, pow_one]
    | succ n ih => rw [pow_succ, pow_mul, ih, hw₀q]
  have hdvd : (p : WittVector p k) ∣ w - teichmuller p w₀ := by
    obtain ⟨y, hy⟩ := exists_eq_p_mul_of_coeff_zero (w - teichmuller p w₀)
      (by rw [sub_coeff_zero, WittVector.teichmuller_coeff_zero, sub_self])
    exact ⟨y, hy⟩
  have hdvdn : ∀ n : ℕ, (p : WittVector p k) ^ ((d : ℕ) * n + 1) ∣
      w - teichmuller p w₀ := by
    intro n
    have h := dvd_sub_pow_of_dvd_sub hdvd ((d : ℕ) * n)
    rwa [pow_mul, ← hcard, hwqn, ← map_pow, hw₀qn] at h
  have hzero : w - teichmuller p w₀ = 0 := by
    apply eq_zero_of_forall_pow_dvd
    intro N
    refine (pow_dvd_pow _ ?_).trans (hdvdn N)
    have : (1 : ℕ) ≤ d := d.pos
    nlinarith
  exact (sub_eq_zero.1 hzero)

private theorem apply_frobenius_teichmuller {p : ℕ} [Fact p.Prime] {F : Type u} [Field F]
    [Finite F] [CharP F p] {k : Type v} [CommRing k] [CharP k p] [PerfectRing k p]
    (ι : WittVector p F →+* WittVector p k) (z : F) :
    ι (frobenius (teichmuller p z)) = frobenius (ι (teichmuller p z)) := by
  have hF : frobenius (teichmuller p z) = teichmuller p z ^ p := by
    rw [WittVector.frobenius_eq_map_frobenius, WittVector.map_teichmuller, frobenius_def, map_pow]
  have hk : ∀ c : k, frobenius (teichmuller p c) = teichmuller p c ^ p := by
    intro c
    rw [WittVector.frobenius_eq_map_frobenius, WittVector.map_teichmuller, frobenius_def, map_pow]
  rw [hF, map_pow, apply_teichmuller_eq ι z, hk]

private theorem main {p : ℕ} [Fact p.Prime] {F : Type u} [Field F] [Finite F] [CharP F p]
    {k : Type v} [CommRing k] [CharP k p] [PerfectRing k p]
    (ι : WittVector p F →+* WittVector p k) (x : WittVector p F) :
    ι (frobenius x) = frobenius (ι x) := by
  set f : WittVector p F →+* WittVector p k := ι.comp frobenius with hf
  set g : WittVector p F →+* WittVector p k :=
    (frobenius : WittVector p k →+* WittVector p k).comp ι
    with hg
  have hfg : Set.EqOn f g (Set.range (teichmuller p : F → WittVector p F)) := by
    rintro _ ⟨z, rfl⟩
    exact apply_frobenius_teichmuller ι z
  have hcl := RingHom.eqOn_set_closure hfg
  suffices h : f x - g x = 0 by
    have hthis := sub_eq_zero.1 h
    simpa [hf, hg] using hthis
  apply eq_zero_of_forall_pow_dvd
  intro N
  obtain ⟨y, hy, z, hz⟩ := exists_mem_closure_add_pow_mul N x
  refine ⟨f z - g z, ?_⟩
  rw [hz, map_add, map_add, hcl hy, map_mul, map_mul, map_pow, map_pow, map_natCast, map_natCast]
  ring

end WittRigidAux

/-- Ring homomorphisms out of Witt vectors over a finite field commute with
Frobenius. -/
theorem WittVector.ringHom_map_frobenius_of_finite (p : ℕ) [Fact p.Prime]
    {F : Type u} [Field F] [Finite F] [CharP F p] {k : Type v} [CommRing k] [CharP k p]
    [PerfectRing k p] (ι : WittVector p F →+* WittVector p k) (x : WittVector p F) :
    ι (WittVector.frobenius x) = WittVector.frobenius (ι x) :=
  WittRigidAux.main ι x

namespace WittCoeffSpanAux

variable {S : Type u} [CommRing S] (p : ℕ) [Fact p.Prime]

omit [Fact p.Prime] in
private theorem mem_of_pow_mem (_hred : IsReduced (S ⧸ Ideal.span {(p : S)})) {a : S} {k : ℕ}
    (_hk : k ≠ 0) (ha : a ^ k ∈ Ideal.span {(p : S)}) : a ∈ Ideal.span {(p : S)} := by
  have ha' : (Ideal.Quotient.mk (Ideal.span {(p : S)}) a) ^ k = 0 := by
    rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]; exact ha
  exact (Ideal.Quotient.eq_zero_iff_mem).mp (IsReduced.eq_zero _ ⟨k, ha'⟩)

private theorem pow_le_pow_pow (N : ℕ) : N ≤ p ^ N :=
  (Nat.lt_pow_self (Nat.Prime.one_lt Fact.out)).le

private theorem main (hp : (p : S) ∈ nonZeroDivisors S)
    (hred : IsReduced (S ⧸ Ideal.span {(p : S)})) :
    ∀ (N : ℕ) (z : ℕ → S),
      (∑ j ∈ Finset.range N, (p : S) ^ j * z j ^ p ^ (N - 1 - j)) ∈
        Ideal.span {(p : S) ^ N} →
      ∀ j, j < N → z j ∈ Ideal.span {(p : S)}
  | 0, z, _, j, hj => absurd hj (Nat.not_lt_zero _)
  | N + 1, z, hz, j, hj => by
    have h0 : z 0 ∈ Ideal.span {(p : S)} := by
      have hsum : (∑ j ∈ Finset.range (N + 1),
          (p : S) ^ j * z j ^ p ^ (N + 1 - 1 - j)) ∈ Ideal.span {(p : S)} := by
        refine Ideal.span_singleton_le_span_singleton.2 ⟨(p : S) ^ N, by ring⟩ hz |> fun h => ?_
        exact h
      rw [Finset.sum_range_succ'] at hsum
      have hrest : (∑ j ∈ Finset.range N,
          (p : S) ^ (j + 1) * z (j + 1) ^ p ^ (N + 1 - 1 - (j + 1))) ∈
          Ideal.span {(p : S)} := by
        refine Ideal.sum_mem _ fun j _ => ?_
        rw [pow_succ', mul_assoc]
        exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
      have hthis := Ideal.sub_mem _ hsum hrest
      rw [add_sub_cancel_left, pow_zero, one_mul] at hthis
      by_cases hN : p ^ (N + 1 - 1 - 0) = 0
      · exact absurd hN (pow_ne_zero _ (Nat.Prime.ne_zero Fact.out))
      · exact mem_of_pow_mem p hred hN hthis
    rcases Nat.eq_zero_or_pos j with rfl | hjpos
    · exact h0
    obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.1 h0
    have hz0 : (p : S) ^ 0 * z 0 ^ p ^ (N + 1 - 1 - 0) ∈ Ideal.span {(p : S) ^ (N + 1)} := by
      rw [pow_zero, one_mul, ← ht, mul_pow]
      simp only [Nat.add_sub_cancel, Nat.sub_zero]
      refine Ideal.mul_mem_left _ _ (Ideal.span_singleton_le_span_singleton.2 ?_
        (Ideal.mem_span_singleton_self _))
      exact pow_dvd_pow _ (Nat.lt_pow_self (Nat.Prime.one_lt Fact.out))
    have hrest : (∑ j ∈ Finset.range N,
        (p : S) ^ (j + 1) * z (j + 1) ^ p ^ (N + 1 - 1 - (j + 1))) ∈
        Ideal.span {(p : S) ^ (N + 1)} := by
      have hthis := Ideal.sub_mem _ hz hz0
      rwa [Finset.sum_range_succ', add_sub_cancel_right] at hthis
    have hfac : (∑ j ∈ Finset.range N,
        (p : S) ^ (j + 1) * z (j + 1) ^ p ^ (N + 1 - 1 - (j + 1))) =
        (p : S) * ∑ j ∈ Finset.range N, (p : S) ^ j * z (j + 1) ^ p ^ (N - 1 - j) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j hj => ?_
      have hthis : N + 1 - 1 - (j + 1) = N - 1 - j := by omega
      rw [hthis, pow_succ']
      ring
    rw [hfac] at hrest
    have hrest' : (∑ j ∈ Finset.range N, (p : S) ^ j * z (j + 1) ^ p ^ (N - 1 - j)) ∈
        Ideal.span {(p : S) ^ N} := by
      obtain ⟨s, hs⟩ := Ideal.mem_span_singleton'.1 hrest
      refine Ideal.mem_span_singleton'.2 ⟨s, ?_⟩
      have hthis : (p : S) * (s * (p : S) ^ N) =
          (p : S) * ∑ j ∈ Finset.range N, (p : S) ^ j * z (j + 1) ^ p ^ (N - 1 - j) := by
        rw [← hs]; ring
      exact (mul_cancel_left_mem_nonZeroDivisors hp).1 hthis
    have ih := main hp hred N (fun j => z (j + 1)) hrest' (j - 1) (by omega)
    have hthis : j - 1 + 1 = j := by omega
    simpa [hthis] using ih

end WittCoeffSpanAux

/-- If a ghost component of a Witt vector is highly `p`-divisible and the
reduction mod `p` is reduced, all lower coefficients lie in `(p)`. -/
theorem WittVector.coeff_mem_span_of_ghostComponent_mem_span_pow_of_isReduced
    {S : Type u} [CommRing S] (p : ℕ) [Fact p.Prime] (hp : (p : S) ∈ nonZeroDivisors S)
    (hred : IsReduced (S ⧸ Ideal.span {(p : S)}))
    (z : WittVector p S) (N : ℕ)
    (hz : WittVector.ghostComponent (N - 1) z ∈ Ideal.span {(p : S) ^ N}) :
    ∀ j : ℕ, j < N → z.coeff j ∈ Ideal.span {(p : S)} := by
  intro j hj
  rcases Nat.eq_zero_or_pos N with rfl | hNpos
  · exact absurd hj (Nat.not_lt_zero _)
  have hN : N - 1 + 1 = N := by omega
  refine WittCoeffSpanAux.main p hp hred N (fun j => z.coeff j) ?_ j hj
  have h := hz
  rw [WittVector.ghostComponent_apply, wittPolynomial_eq_sum_C_mul_X_pow, map_sum, hN] at h
  simp only [map_mul, map_pow, MvPolynomial.aeval_X, map_natCast] at h
  exact h
