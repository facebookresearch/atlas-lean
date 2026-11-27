/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.Set.Card
public import Mathlib.Data.ZMod.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

open Finset Polynomial

namespace MathlibExt.Combinatorics.ZeroSumFixedLengthTwoResiduesErdosProblem541Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #541, https://www.erdosproblems.com/541 (status PROVED
(LEAN)). UnsolvedMath record UM-30006924 (`EP-541`), dataset ulamai/UnsolvedMath v1.8.0.

Stated for primes as posed; Gao, Hamidoune and Wang proved it for every modulus. Compared with the
formal-conjectures statement `ErdosProblems/541.lean` (equivalent to `erdos_541`; no code imported).
-/

/-
The statement is the prime case of Gao–Hamidoune–Wang, Theorem 1.1 (arXiv:0902.4758).
We use an independent finite-difference proof. Over the prime field the indicator of a
zero-sum subset is `1` minus its sum raised to `p - 1`. Weighting its alternating subset
sum by the number of omitted indices gives an identity involving one-index deletions.
The top two finite differences turn these identities into a single quadratic satisfied
by every entry, except in the boundary cases handled separately below.
-/

section Differences

variable {ι K : Type*} [CommRing K]

/-- The iterated signed difference, with the empty subset carrying sign `+1`. -/
private noncomputable def alt (a : ι → K) (s : Finset ι) (f : K[X]) : K[X] :=
  ∑ t ∈ s.powerset, ((-1 : K) ^ t.card) • taylor (∑ i ∈ t, a i) f

private lemma alt_insert [DecidableEq ι] (a : ι → K) (s : Finset ι) (f : K[X])
    {i : ι} (hi : i ∉ s) :
    alt a (insert i s) f = alt a s f - taylor (a i) (alt a s f) := by
  unfold alt
  rw [sum_powerset_insert hi, map_sum, sub_eq_add_neg, ← sum_neg_distrib]
  congr 1
  apply sum_congr rfl
  intro t ht
  have hit : i ∉ t := fun h ↦ hi ((mem_powerset.mp ht) h)
  simp [card_insert_of_notMem hit, sum_insert hit, pow_succ, map_smul, taylor_taylor]

/-- A difference lowers the degree by one; this is the coefficient at the new bound. -/
private lemma coeff_sub_taylor (f : K[X]) (z : K) (n : ℕ) (h : f.natDegree ≤ n + 1) :
    (f - taylor z f).coeff n = - (n + 1 : K) * z * f.coeff (n + 1) := by
  have H : hasseDeriv n f = C (f.coeff n) + C ((n + 1 : K) * f.coeff (n + 1)) * X := by
    ext k
    simp only [hasseDeriv_coeff, coeff_add, coeff_C, coeff_C_mul_X]
    rcases k with _ | _ | k
    · simp
    · simp [Nat.add_comm 1 n, Nat.choose_succ_self_right]
    · have hz := coeff_eq_zero_of_natDegree_lt (p := f) (n := k + 2 + n) (by omega)
      simp [hz]
  rw [coeff_sub, taylor_coeff, H]
  simp
  ring

private lemma natDegree_sub_taylor_le (f : K[X]) (z : K) (n : ℕ)
    (h : f.natDegree ≤ n + 1) : (f - taylor z f).natDegree ≤ n := by
  refine natDegree_le_iff_coeff_eq_zero.mpr fun k hk ↦ ?_
  rw [coeff_sub_taylor f z k (by omega), coeff_eq_zero_of_natDegree_lt (by omega), mul_zero]

private lemma alt_degree (a : ι → K) (s : Finset ι) (f : K[X]) (N : ℕ)
    (hf : f.natDegree ≤ N) : (alt a s f).natDegree ≤ N - s.card := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa [alt] using hf
  | @insert i s hi ih =>
    rw [alt_insert a s f hi, card_insert_of_notMem hi]
    apply natDegree_sub_taylor_le
    omega

private lemma alt_eq_zero_of_lt (a : ι → K) (s : Finset ι) (f : K[X])
    (h : f.natDegree < s.card) : alt a s f = 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp at h
  | @insert i s hi ih =>
    rw [alt_insert a s f hi]
    have hd := alt_degree a s f f.natDegree le_rfl
    rw [card_insert_of_notMem hi] at h
    have hc : (alt a s f).natDegree ≤ 0 := by omega
    rw [eq_C_of_natDegree_le_zero hc, taylor_C, sub_self]

private lemma alt_coeff (a : ι → K) (s : Finset ι) (f : K[X]) (N : ℕ)
    (hf : f.natDegree ≤ N) (hs : s.card ≤ N) :
    (alt a s f).coeff (N - s.card) =
      (∏ i ∈ s, a i) * (∏ j ∈ range s.card, - ((N - j : ℕ) : K)) * f.coeff N := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [alt]
  | @insert i s hi ih =>
    rw [card_insert_of_notMem hi] at hs ⊢
    rw [alt_insert a s f hi, coeff_sub_taylor, show N - (s.card + 1) + 1 = N - s.card by omega,
      ih (by omega), prod_insert hi, prod_range_succ]
    · rw [← Nat.cast_one (R := K), ← Nat.cast_add,
        show N - (s.card + 1) + 1 = N - s.card by omega]
      ring
    · have hd := alt_degree a s f N hf
      omega

private lemma eval_alt (a : ι → K) (s : Finset ι) (f : K[X]) (x : K) :
    (alt a s f).eval x = ∑ t ∈ s.powerset, (-1 : K) ^ t.card * f.eval (x + ∑ i ∈ t, a i) := by
  simp [alt, eval_finsetSum, smul_eq_C_mul, eval_mul, taylor_eval]

private lemma eval_alt_top (a : ι → K) (s : Finset ι) (m : ℕ) (hm : s.card = m) :
    (alt a s (X ^ m)).eval 0 = (∏ i ∈ s, a i) * (∏ j ∈ range m, - ((m - j : ℕ) : K)) := by
  have hc := alt_coeff a s (X ^ m) m (natDegree_X_pow_le m) hm.le
  simpa [hm, coeff_X_pow, coeff_zero_eq_eval_zero] using hc

/-- Complementing the subset reverses the next-to-top difference about the midpoint. -/
private lemma eval_alt_complement (a : ι → K) (s : Finset ι) (m : ℕ) (hm : s.card + 1 = m) :
    (alt a s (X ^ m)).eval (-(∑ i ∈ s, a i)) = -(alt a s (X ^ m)).eval 0 := by
  classical
  simp only [eval_alt, eval_pow, eval_X, zero_add]
  conv_rhs => rw [← sum_neg_distrib]
  refine sum_bij (fun t _ ↦ s \ t) (fun _ _ ↦ mem_powerset.mpr sdiff_subset) ?_ ?_ ?_
  · intro t ht u hu he
    have h1 : s \ (s \ t) = t := Finset.sdiff_sdiff_eq_self (mem_powerset.mp ht)
    have h2 : s \ (s \ u) = u := Finset.sdiff_sdiff_eq_self (mem_powerset.mp hu)
    rw [← h1, ← h2, he]
  · intro t ht
    exact ⟨s \ t, mem_powerset.mpr sdiff_subset, Finset.sdiff_sdiff_eq_self (mem_powerset.mp ht)⟩
  · intro t ht
    have ht' := mem_powerset.mp ht
    have hsum : -(∑ i ∈ s, a i) + ∑ i ∈ t, a i = -(∑ i ∈ s \ t, a i) := by
      rw [← sum_sdiff ht' (f := a)]
      ring
    rw [hsum]
    have hpow (z : K) : (-z) ^ m = (-1 : K) ^ m * z ^ m := by
      rw [← mul_pow, neg_one_mul]
    rw [hpow]
    have hcard : m = (s \ t).card + (t.card + 1) := by
      have := card_sdiff_add_card_eq_card ht'
      omega
    have hsign : (-1 : K) ^ t.card * (-1 : K) ^ m = -((-1 : K) ^ (s \ t).card) := by
      conv_lhs => arg 2; rw [hcard, pow_add, pow_succ]
      have hsquare : (-1 : K) ^ t.card * (-1 : K) ^ t.card = 1 := by
        rw [← mul_pow, neg_mul_neg, one_mul, one_pow]
      calc
        _ = -(((-1 : K) ^ t.card * (-1) ^ t.card) * (-1) ^ (s \ t).card) := by ring
        _ = _ := by rw [hsquare, one_mul]
    rw [← mul_assoc, hsign, neg_mul]

private lemma eval_alt_next (a : ι → K) (s : Finset ι) (m : ℕ) (hm : s.card + 1 = m) :
    2 * (alt a s (X ^ m)).eval 0 =
      -((∏ i ∈ s, a i) * (∏ j ∈ range m, - ((m - j : ℕ) : K)) * (∑ i ∈ s, a i)) := by
  let q := alt a s (X ^ m)
  have hd := alt_degree a s (X ^ m) m (natDegree_X_pow_le m)
  have hdeg : q.natDegree ≤ 1 := by dsimp [q]; omega
  have hlinear := eq_X_add_C_of_natDegree_le_one hdeg
  have hs := eval_alt_complement a s m hm
  change q.eval (-(∑ i ∈ s, a i)) = -q.eval 0 at hs
  have he (x : K) : q.eval x = q.coeff 1 * x + q.coeff 0 := by
    conv_lhs => rw [hlinear]
    simp
  rw [he, he] at hs
  rw [he, mul_zero, zero_add]
  have hc := alt_coeff a s (X ^ m) m (natDegree_X_pow_le m) (by omega)
  rw [show m - s.card = 1 by omega] at hc
  simp only [coeff_X_pow, ite_true, mul_one] at hc
  change q.coeff 1 = _ at hc
  rw [← hm, prod_range_succ, show s.card + 1 - s.card = 1 by omega, Nat.cast_one, mul_neg_one]
  rw [← hm] at hc
  linear_combination hs + (∑ i ∈ s, a i) * hc

end Differences

section Indicator

variable {ι : Type*} {p : ℕ} [Fact p.Prime]

private noncomputable def difference (a : ι → ZMod p) (s : Finset ι) : ZMod p :=
  (alt a s (X ^ (p - 1))).eval 0

private def zeroIndicator (a : ι → ZMod p) (t : Finset ι) : ZMod p :=
  if ∑ i ∈ t, a i = 0 then (-1) ^ t.card else 0

private lemma pow_prime_sub_one {x : ZMod p} (hx : x ≠ 0) : x ^ (p - 1) = 1 := by
  have h := pow_card_eq_one' (x := Units.mk0 x hx)
  rw [Nat.card_units, Nat.card_zmod] at h
  exact congrArg (fun u : (ZMod p)ˣ ↦ (u : ZMod p)) h

private lemma sum_zeroIndicator (a : ι → ZMod p) {s : Finset ι} (hs : s.Nonempty) :
    ∑ t ∈ s.powerset, zeroIndicator a t = -difference a s := by
  have hp : p - 1 ≠ 0 := by have := (Fact.out : p.Prime).two_le; omega
  have hpoint (t : Finset ι) :
      zeroIndicator a t = (-1) ^ t.card * (1 - (∑ i ∈ t, a i) ^ (p - 1)) := by
    unfold zeroIndicator
    split_ifs with h
    · simp [h, zero_pow hp]
    · simp [pow_prime_sub_one h]
  have hcancel : ∑ t ∈ s.powerset, (-1 : ZMod p) ^ t.card = 0 := by
    have h := alt_eq_zero_of_lt a s (1 : (ZMod p)[X]) (by simpa using hs.card_pos)
    simpa [eval_alt] using congrArg (fun q : (ZMod p)[X] ↦ q.eval 0) h
  simp only [hpoint, mul_sub, mul_one, sum_sub_distrib, hcancel, zero_sub, difference,
    eval_alt, eval_pow, eval_X, zero_add]

private lemma difference_eq_neg_one (a : ι → ZMod p) {s : Finset ι} (hs : s.Nonempty)
    (hfree : ∀ t ⊆ s, t.Nonempty → ∑ i ∈ t, a i ≠ 0) : difference a s = -1 := by
  have h : ∑ t ∈ s.powerset, zeroIndicator a t = 1 := by
    rw [sum_eq_single ∅]
    · simp [zeroIndicator]
    · intro t ht hne
      simp [zeroIndicator, hfree t (mem_powerset.mp ht) (nonempty_iff_ne_empty.mpr hne)]
    · simp
  rw [sum_zeroIndicator a hs] at h
  linear_combination -h

/-- Double count pairs consisting of a subset and an index it omits. -/
private lemma sum_erase_powersets [DecidableEq ι] {K : Type*} [Ring K]
    (s : Finset ι) (g : Finset ι → K) :
    ∑ i ∈ s, ∑ t ∈ (s.erase i).powerset, g t =
      ∑ t ∈ s.powerset, ((s.card : K) - (t.card : K)) * g t := by
  have h (i : ι) : (s.erase i).powerset = s.powerset.filter (fun t ↦ i ∉ t) := by
    ext t
    simp [subset_erase]
  simp only [h, sum_filter]
  rw [sum_comm]
  apply sum_congr rfl
  intro t ht
  rw [← sum_filter]
  have he : s.filter (fun i ↦ i ∉ t) = s \ t := by ext i; simp
  rw [he, sum_const, nsmul_eq_mul, card_sdiff_of_subset (mem_powerset.mp ht),
    Nat.cast_sub (card_le_card (mem_powerset.mp ht))]

/-- Weight the zero-sum indicator by the number of indices omitted. Nonempty zero sums
all have size `r`; the empty subset contributes the correction term `r`. -/
private lemma difference_moment [DecidableEq ι] (a : ι → ZMod p) (r : ℕ) (s : Finset ι)
    (hs : 2 ≤ s.card)
    (hr : ∀ t : Finset ι, t.Nonempty → ∑ i ∈ t, a i = 0 → t.card = r) :
    ((s.card : ZMod p) - r) * difference a s - ∑ i ∈ s, difference a (s.erase i) = r := by
  have H := sum_erase_powersets s (zeroIndicator a)
  have hne : s.Nonempty := card_pos.mp (by omega)
  have herase (i : ι) (hi : i ∈ s) : (s.erase i).Nonempty := by
    rw [← card_pos, card_erase_of_mem hi]
    omega
  have hleft : (∑ i ∈ s, ∑ t ∈ (s.erase i).powerset, zeroIndicator a t) =
      -(∑ i ∈ s, difference a (s.erase i)) := by
    rw [← sum_neg_distrib]
    exact sum_congr rfl fun i hi ↦ sum_zeroIndicator a (herase i hi)
  have hpoint (t : Finset ι) : ((s.card : ZMod p) - t.card) * zeroIndicator a t =
      ((s.card : ZMod p) - r) * zeroIndicator a t + if t = ∅ then (r : ZMod p) else 0 := by
    by_cases ht : t = ∅
    · subst t
      simp [zeroIndicator]
    · by_cases hz : ∑ i ∈ t, a i = 0
      · simp [ht, hr t (nonempty_iff_ne_empty.mpr ht) hz]
      · simp [ht, zeroIndicator, hz]
  rw [hleft] at H
  simp only [hpoint, sum_add_distrib, ← mul_sum, sum_ite_eq', empty_mem_powerset,
    ite_true, sum_zeroIndicator a hne] at H
  linear_combination H

private def scale (p : ℕ) : ZMod p :=
  ∏ j ∈ range (p - 1), - (((p - 1) - j : ℕ) : ZMod p)

private lemma difference_top (a : ι → ZMod p) (s : Finset ι) (hs : s.card = p - 1) :
    difference a s = (∏ i ∈ s, a i) * scale p :=
  eval_alt_top a s (p - 1) hs

private lemma difference_next (a : ι → ZMod p) (s : Finset ι) (hs : s.card + 1 = p - 1) :
    2 * difference a s = -((∏ i ∈ s, a i) * scale p * (∑ i ∈ s, a i)) :=
  eval_alt_next a s (p - 1) hs

private lemma difference_full (a : ι → ZMod p) (s : Finset ι) (hs : s.card = p) :
    difference a s = 0 := by
  have hp := (Fact.out : p.Prime).two_le
  have hdeg := natDegree_X_pow_le (R := ZMod p) (p - 1)
  have hz := alt_eq_zero_of_lt a s (X ^ (p - 1)) (by omega)
  simp [difference, hz]

private lemma prod_erase_eq_mul_inv [DecidableEq ι] (a : ι → ZMod p) (s : Finset ι) {i : ι}
    (hi : i ∈ s) (hnz : a i ≠ 0) : (∏ j ∈ s.erase i, a j) = (∏ j ∈ s, a j) * (a i)⁻¹ := by
  rw [← prod_erase_mul s a hi, mul_assoc, mul_inv_cancel₀ hnz, mul_one]

private lemma sum_difference_next [DecidableEq ι] (a : ι → ZMod p) (s : Finset ι)
    (hs : s.card = p - 1)
    (hnz : ∀ i ∈ s, a i ≠ 0) :
    2 * (∑ i ∈ s, difference a (s.erase i)) =
      -(difference a s * ((∑ i ∈ s, a i) * (∑ i ∈ s, (a i)⁻¹) - s.card)) := by
  have hp := (Fact.out : p.Prime).two_le
  rw [mul_sum]
  calc
    _ = ∑ i ∈ s, -(difference a s * ((∑ j ∈ s, a j) * (a i)⁻¹ - 1)) := by
      apply sum_congr rfl
      intro i hi
      have hc := card_erase_of_mem hi
      rw [difference_next a (s.erase i) (by omega), difference_top a s hs,
        prod_erase_eq_mul_inv a s hi (hnz i hi)]
      have hsum : (∑ j ∈ s.erase i, a j) = (∑ j ∈ s, a j) - a i := by
        rw [← sum_erase_add s a hi, add_sub_cancel_right]
      rw [hsum]
      have hinv := mul_inv_cancel₀ (hnz i hi)
      linear_combination ((∏ j ∈ s, a j) * scale p) * hinv
    _ = _ := by
      simp only [sum_neg_distrib, ← mul_sum, sum_sub_distrib, sum_const, nsmul_eq_mul, mul_one]

/-- On `p - 1` indices without a nonempty zero-sum, comparison with each deletion
shows that every entry is the negative of the total. -/
private lemma eq_neg_sum_of_zeroFree (a : ι → ZMod p) (s : Finset ι) (hp : 3 ≤ p)
    (hs : s.card = p - 1) (hfree : ∀ t ⊆ s, t.Nonempty → ∑ j ∈ t, a j ≠ 0)
    {i : ι} (hi : i ∈ s) : a i = -(∑ j ∈ s, a j) := by
  classical
  have h := difference_eq_neg_one a (s := s) (card_pos.mp (by omega)) hfree
  rw [difference_top a s hs] at h
  have hc := card_erase_of_mem hi
  have h' := difference_eq_neg_one a (s := s.erase i) (card_pos.mp (by omega))
    (fun t ht ↦ hfree t (ht.trans (erase_subset i s)))
  have hnext := difference_next a (s.erase i) (by omega)
  rw [h'] at hnext
  have hprod := prod_erase_mul s a hi
  have hsum := sum_erase_add s a hi
  linear_combination -(a i) * hnext + ((∑ j ∈ s.erase i, a j) * scale p) * hprod +
    (∑ j ∈ s.erase i, a j) * h - hsum

end Indicator

private lemma ncard_range_le_two_of_mem_pair {ι K : Type*} (a : ι → K) (x y : K)
    (h : ∀ i, a i = x ∨ a i = y) : (Set.range a).ncard ≤ 2 := by
  classical
  have hs : Set.range a ⊆ (↑({x, y} : Finset K) : Set K) := by
    rintro _ ⟨i, rfl⟩
    simpa using h i
  refine (Set.ncard_le_ncard hs).trans ?_
  rw [Set.ncard_coe_finset]
  exact (card_insert_le x {y}).trans (by simp)

private lemma ncard_range_le_two_of_quadratic {ι K : Type*} [Field K] (a : ι → K)
    {u v w : K} (hu : u ≠ 0) (hroot : ∀ i, u * (a i) ^ 2 + v * a i + w = 0) :
    (Set.range a).ncard ≤ 2 := by
  classical
  let f : K[X] := C u * X ^ 2 + C v * X + C w
  have hcoef : f.coeff 2 = u := by simp [f]
  have hf : f ≠ 0 := fun h ↦ hu (by simpa [h] using hcoef.symm)
  have hdeg : f.natDegree ≤ 2 := by
    refine natDegree_le_iff_coeff_eq_zero.mpr fun n hn ↦ ?_
    have h0 : n ≠ 0 := by omega
    have h1 : 1 ≠ n := by omega
    have h2 : n ≠ 2 := by omega
    simp [f, coeff_X, coeff_C, h0, h1, h2]
  have hsub : Set.range a ⊆ (↑f.roots.toFinset : Set K) := by
    rintro _ ⟨i, rfl⟩
    simp only [mem_coe, Multiset.mem_toFinset, mem_roots hf, IsRoot, f, eval_add, eval_mul,
      eval_pow, eval_C, eval_X]
    exact hroot i
  exact (Set.ncard_le_ncard hsub).trans (by
    rw [Set.ncard_coe_finset]
    exact (Multiset.toFinset_card_le _).trans ((card_roots' f).trans hdeg))

private lemma graham_prime (p : ℕ) (hp : p.Prime) (a : Fin p → ZMod p) (r : ℕ)
    (hr : ∀ t : Finset (Fin p), t.Nonempty → ∑ i ∈ t, a i = 0 → t.card = r) :
    (Set.range a).ncard ≤ 2 := by
  let : Fact p.Prime := ⟨hp⟩
  have hp2 := hp.two_le
  by_cases htwo : p = 2
  · subst p
    exact (Set.ncard_le_ncard (Set.subset_univ (Set.range a))).trans (by simp)
  have hp3 : 3 ≤ p := by omega
  let T : Finset (Fin p) := univ
  have hcardT : T.card = p := by simp [T]
  have hinT (i : Fin p) : i ∈ T := mem_univ i
  have hcard (i : Fin p) : (T.erase i).card = p - 1 := by
    rw [card_erase_of_mem (hinT i), hcardT]
  have hfull : difference a T = 0 := difference_full a T hcardT
  by_cases hr0 : r = 0
  · have hfree : ∀ t ⊆ T, t.Nonempty → ∑ i ∈ t, a i ≠ 0 := by
      intro t _ ht hz
      have := hr t ht hz
      have := ht.card_pos
      omega
    have hz := difference_eq_neg_one a (s := T) (card_pos.mp (by omega)) hfree
    rw [hfull] at hz
    exact (neg_ne_zero.mpr one_ne_zero hz.symm).elim
  by_cases hrp : p ≤ r
  · -- Every deletion is zero-sum-free; their top differences are the same.
    have hval (i : Fin p) : (∏ j ∈ T, a j) * scale p = -a i := by
      have hfree : ∀ t ⊆ T.erase i, t.Nonempty → ∑ j ∈ t, a j ≠ 0 := by
        intro t ht hne hz
        have := hr t hne hz
        have := card_le_card ht
        have := hcard i
        omega
      have hs : (T.erase i).Nonempty := card_pos.mp (by have := hcard i; omega)
      have h := difference_eq_neg_one a hs hfree
      rw [difference_top a (T.erase i) (hcard i)] at h
      have hprod := mul_prod_erase T a (hinT i)
      linear_combination a i * h - scale p * hprod
    refine ncard_range_le_two_of_mem_pair a (a ⟨0, by omega⟩) 0 fun i ↦ Or.inl ?_
    exact neg_injective ((hval i).symm.trans (hval _))
  by_cases hzero : ∃ i, a i = 0
  · obtain ⟨i, hi⟩ := hzero
    have hr1 : 1 = r := by simpa using hr {i} (singleton_nonempty i) (by simpa using hi)
    have hfree : ∀ t ⊆ T.erase i, t.Nonempty → ∑ j ∈ t, a j ≠ 0 := by
      intro t ht hne hz
      have hit := (subset_erase.mp ht).2
      have h1 := hr t hne hz
      have h2 := hr (insert i t) (insert_nonempty _ _) (by simp [sum_insert hit, hi, hz])
      rw [card_insert_of_notMem hit] at h2
      omega
    refine ncard_range_le_two_of_mem_pair a 0 (-(∑ j ∈ T.erase i, a j)) fun j ↦ ?_
    by_cases hji : j = i
    · exact Or.inl (hji ▸ hi)
    · exact Or.inr (eq_neg_sum_of_zeroFree a (T.erase i) hp3 (hcard i) hfree
        (mem_erase.mpr ⟨hji, hinT j⟩))
  have hnz (i : Fin p) : a i ≠ 0 := fun h ↦ hzero ⟨i, h⟩
  let A : ZMod p := ∑ i ∈ T, a i
  let H : ZMod p := ∑ i ∈ T, (a i)⁻¹
  let B : ZMod p := (∏ i ∈ T, a i) * scale p
  have htop (i : Fin p) : difference a (T.erase i) = B * (a i)⁻¹ := by
    rw [difference_top a (T.erase i) (hcard i), prod_erase_eq_mul_inv a T (hinT i) (hnz i)]
    dsimp [B]
    ring
  -- The full moment gives `-B * H = r`. In particular the leading coefficient is nonzero.
  have hBH : -(B * H) = (r : ZMod p) := by
    have h := difference_moment a r T (by omega) hr
    simpa only [hfull, mul_zero, zero_sub, htop, ← mul_sum, H] using h
  have hrCast : (r : ZMod p) ≠ 0 := by
    intro h
    have hd := (ZMod.natCast_eq_zero_iff r p).mp h
    exact (not_le_of_gt (by omega : r < p)) (Nat.le_of_dvd (by omega) hd)
  have hB : B ≠ 0 := fun h ↦ hrCast (by simpa [h] using hBH.symm)
  have hH : H ≠ 0 := fun h ↦ hrCast (by simpa [h] using hBH.symm)
  refine ncard_range_le_two_of_quadratic a hH (v := A * H - 2 * r) (w := -A) fun i ↦ ?_
  let U := T.erase i
  let Q := difference a U
  have hcardU : U.card = p - 1 := hcard i
  have hcastU : (U.card : ZMod p) = -1 := by
    rw [hcardU, Nat.cast_sub (by omega : 1 ≤ p), ZMod.natCast_self, Nat.cast_one, zero_sub]
  have hsumA : (∑ j ∈ U, a j) = A - a i := by
    dsimp [A, U]
    rw [← sum_erase_add T a (hinT i), add_sub_cancel_right]
  have hsumH : (∑ j ∈ U, (a j)⁻¹) = H - (a i)⁻¹ := by
    dsimp [H, U]
    rw [← sum_erase_add T (fun j ↦ (a j)⁻¹) (hinT i), add_sub_cancel_right]
  have hmoment := difference_moment a r U (by omega) hr
  have hnext := sum_difference_next a U hcardU (fun j _ ↦ hnz j)
  rw [hcastU] at hmoment
  rw [hcastU, hsumA, hsumH] at hnext
  change _ * Q - _ = _ at hmoment
  change _ = -(Q * _) at hnext
  -- The deletion moment, followed by the full moment, eliminates its alternating sums.
  have hQ : Q * ((A - a i) * (H - (a i)⁻¹) - 1 - 2 * r) = 2 * r := by
    linear_combination 2 * hmoment + hnext
  have hinv := mul_inv_cancel₀ (hnz i)
  have hiQ : a i * Q = B := by
    change a i * difference a (T.erase i) = B
    rw [htop, mul_left_comm, hinv, mul_one]
  have hdel : (A - a i) * (H - (a i)⁻¹) - 1 - 2 * r = -2 * a i * H := by
    apply mul_left_cancel₀ hB
    linear_combination a i * hQ - ((A - a i) * (H - (a i)⁻¹) - 1 - 2 * r) * hiQ -
      2 * a i * hBH
  linear_combination a i * hdel + (A - a i) * hinv

/-- **Graham's zero-sum statement (Erdős Problem 541).** This is the statement that for every
prime $p$ and every sequence $a_0, \dots, a_{p-1}$ of residues modulo $p$, not necessarily
distinct, if there is a natural number $r$ such that every nonempty set
$S \subseteq \{0, \dots, p-1\}$ with $\sum_{i \in S} a_i = 0$ in $\mathbb{Z}/p\mathbb{Z}$ has
exactly $r$ elements, then at most two distinct residues occur among $a_0, \dots, a_{p-1}$. -/
@[expose] public def fixedZeroSumLengthTwoResidues : Prop :=
  ∀ p : ℕ, p.Prime → ∀ a : Fin p → ZMod p,
    (∃ r : ℕ, ∀ S : Finset (Fin p), S.Nonempty → ∑ i ∈ S, a i = 0 → S.card = r) →
      (Set.range a).ncard ≤ 2

/--
**Zero sums of a single length use at most two residues (Erdős Problem 541).** For every prime
$p$ and every sequence $a_0, \dots, a_{p-1}$ of residues modulo $p$, not necessarily distinct, if
there is a natural number $r$ such that every nonempty set $S \subseteq \{0, \dots, p-1\}$ with
$\sum_{i \in S} a_i = 0$ in $\mathbb{Z}/p\mathbb{Z}$ has exactly $r$ elements, then at most two
distinct residues occur among $a_0, \dots, a_{p-1}$.

Resolved true: Erdős and Szemerédi proved it for all large primes $p$, and Gao, Hamidoune and Wang
for every modulus.

Source: T. F. Bloom, Erdős Problems, Problem #541,
https://www.erdosproblems.com/541 (status PROVED (LEAN)); resolution: W. Gao, Y. O. Hamidoune and G.
Wang, Distinct length modular zero-sum subsequences: a proof of Graham's conjecture, J. Number
Theory (2010), 1425-1431, erdosproblems.com/541: proved by Erdős and Szemerédi for large p and by
Gao, Hamidoune and Wang for all moduli, https://www.erdosproblems.com/541.
-/
public theorem fixedZeroSumLengthTwoResidues_holds : fixedZeroSumLengthTwoResidues := by
  intro p hp a ⟨r, hr⟩
  exact graham_prime p hp a r hr

end MathlibExt.Combinatorics.ZeroSumFixedLengthTwoResiduesErdosProblem541Wanted
