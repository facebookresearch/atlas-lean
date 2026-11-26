/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Nth
public import Mathlib.NumberTheory.AlmostPrime
public import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import MathlibExt.NumberTheory.PrimeCounting.LandauAlmostPrimeAsymptotic

/-!
# Almost primes of almost prime index

The reciprocal sum over an iterated almost prime index set with at least two positive factor
counts converges (`summable_inv_almostPrimeIndexSet`), and these sums tend to zero when the last
factor count grows and at least two positive factor counts are fixed
(`tendsto_tsum_inv_almostPrimeIndexSet_append_zero`).

Both rest on Landau's asymptotic for the number of `k`-almost primes up to `x`: the `n`th
`k`-almost prime is eventually at least `n (log n)^(3/4)`, so the composition of two one-based
enumerations is eventually at least `n (log n)^(3/2)`, and Cauchy condensation applies.
-/

namespace MetaMathlibExt

open Filter Topology

@[expose] public section

/-- **Almost primes of almost prime index.** For natural numbers $k_1, \dots, k_m$ with $m \ge 1$,
the set $N_{k_1 \cdots k_m}$ of natural numbers is defined by recursion on $m$: $N_{k_1}$ is the
set of $k_1$-almost primes (the $n \ne 0$ with exactly $k_1$ prime factors counted with
multiplicity), and for $m \ge 2$, $N_{k_1 \cdots k_m}$ is the set of the $i$th $k_1$-almost
primes, in increasing order and counted from $1$, for $i \ge 1$ in $N_{k_2 \cdots k_m}$. When
there are fewer than $i$ $k_1$-almost primes (only for $k_1 = 0$, where $1$ is the only one),
the $i$th one is taken to be $0$.

Source: Paul Kinlaw, Megan Triplett, and William Tripp, *Almost Primes of Almost Prime Index*,
INTEGERS 24 (2024), Article A99, Section 1 (definitions of `N_k`, `N_{j,k}`, and
`N_{k_1 ⋯ k_m}`). -/
public def almostPrimeIndexSet (k : ℕ) : List ℕ → Set ℕ
  | [] => {n | Nat.IsAlmostPrime k n}
  | j :: L => {n | ∃ i ∈ almostPrimeIndexSet j L, 1 ≤ i ∧ n = Nat.nth (Nat.IsAlmostPrime k) (i - 1)}

/-- **Almost prime index sets with one index.** For every natural number $k$, the almost prime
index set $N_k$ with the single index $k$ is the set of $k$-almost primes, the natural numbers
$n \ne 0$ with exactly $k$ prime factors counted with multiplicity.

Source: Paul Kinlaw, Megan Triplett, and William Tripp, *Almost Primes of Almost Prime Index*,
INTEGERS 24 (2024), Article A99, Section 1 (definition of `N_k`). -/
public theorem almostPrimeIndexSet_nil (k : ℕ) :
    almostPrimeIndexSet k [] = {n | Nat.IsAlmostPrime k n} := rfl

/-- **Membership in an almost prime index set.** For natural numbers $k$, $j$, $n$ and
$\ell_1, \dots, \ell_r$ (with $r \ge 0$), $n$ lies in the almost prime index set
$N_{k j \ell_1 \cdots \ell_r}$ if and only if there is an $i \ge 1$ in $N_{j \ell_1 \cdots \ell_r}$
such that $n$ is the $i$th $k$-almost prime in increasing order, counted from $1$ (taken to be $0$
if there are fewer than $i$ of them).

Source: Paul Kinlaw, Megan Triplett, and William Tripp, *Almost Primes of Almost Prime Index*,
INTEGERS 24 (2024), Article A99, Section 1 (definition of `N_{k_1 ⋯ k_m}`). -/
public theorem mem_almostPrimeIndexSet_cons (k j : ℕ) (L : List ℕ) (n : ℕ) :
    n ∈ almostPrimeIndexSet k (j :: L) ↔
      ∃ i ∈ almostPrimeIndexSet j L, 1 ≤ i ∧ n = Nat.nth (Nat.IsAlmostPrime k) (i - 1) :=
  Iff.rfl

end

namespace AlmostPrimeIndex

private lemma infinite_almostPrimes {k : ℕ} (hk : 1 ≤ k) :
    (Set.ofPred (Nat.IsAlmostPrime k)).Infinite := by
  refine Set.infinite_iff_exists_gt.mpr fun n ↦ ?_
  obtain ⟨p, hnp, hp⟩ := Nat.exists_infinite_primes (n + 1)
  refine ⟨p ^ k, ⟨pow_ne_zero _ hp.ne_zero, ArithmeticFunction.cardFactors_apply_prime_pow hp⟩, ?_⟩
  exact lt_of_lt_of_le hnp (by simpa using Nat.pow_le_pow_right hp.pos hk)

/-- One-based enumeration, extended by zero at index zero. -/
private noncomputable def enum (k : ℕ) : ℕ → ℕ
  | 0 => 0
  | i + 1 => Nat.nth (Nat.IsAlmostPrime k) i

private lemma enum_strictMono {k : ℕ} (hk : 1 ≤ k) : StrictMono (enum k) := by
  apply strictMono_nat_of_lt_succ
  rintro (_ | n)
  · exact Nat.pos_of_ne_zero (Nat.nth_mem_of_infinite (infinite_almostPrimes hk) 0).1
  · exact Nat.nth_strictMono (infinite_almostPrimes hk) (Nat.lt_succ_self n)

private lemma count_enum {k : ℕ} (hk : 1 ≤ k) (i : ℕ) :
    almostPrimeCounting k (enum k i) = i := by
  cases i with
  | zero => simp [enum, almostPrimeCounting]
  | succ i =>
    change almostPrimeCounting k (Nat.nth _ i) = i + 1
    rw [← Nat.count_nth_succ_of_infinite (infinite_almostPrimes hk) i,
      Nat.count_eq_card_filter_range]
    unfold almostPrimeCounting
    congr 1
    ext n
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_range]
    exact ⟨fun ⟨⟨_, h⟩, hp⟩ ↦ ⟨by omega, hp⟩,
      fun ⟨h, hp⟩ ↦ ⟨⟨Nat.pos_of_ne_zero hp.1, by omega⟩, hp⟩⟩

/-- A fixed power of the iterated logarithm costs at most a quarter power of the logarithm
in Landau's counting estimate. -/
private lemma count_mul_log_le {k : ℕ} (hk : 1 ≤ k) :
    ∀ᶠ x : ℕ in atTop,
      (almostPrimeCounting k x : ℝ) * Real.log x ^ (3 / 4 : ℝ) ≤ x := by
  obtain ⟨C, hC, hbound⟩ := (landau_almostPrimeCounting_isEquivalent k hk).isBigO.exists_pos
  have hlog := (isLittleO_log_rpow_rpow_atTop ((k - 1 : ℕ) : ℝ)
    (show (0 : ℝ) < 1 / 4 by norm_num)).comp_tendsto
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  filter_upwards [hbound.bound, hlog.bound (inv_pos.mpr hC),
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1]
    with x hcount hsmall hx
  change 1 ≤ Real.log (x : ℝ) at hx
  have hL : 0 < Real.log (x : ℝ) := by linarith
  have hLL : 0 ≤ Real.log (Real.log (x : ℝ)) := Real.log_nonneg hx
  have hfac : (1 : ℝ) ≤ (k - 1).factorial := by exact_mod_cast Nat.factorial_pos (k - 1)
  simp only [Function.comp_apply, Real.rpow_natCast] at hsmall
  rw [Real.norm_of_nonneg (pow_nonneg hLL _),
    Real.norm_of_nonneg (Real.rpow_nonneg hL.le _)] at hsmall
  have hnum : C * Real.log (Real.log (x : ℝ)) ^ (k - 1) ≤ Real.log x ^ (1 / 4 : ℝ) := by
    calc
      _ ≤ C * (C⁻¹ * Real.log x ^ (1 / 4 : ℝ)) := by gcongr
      _ = _ := by field_simp
  rw [Real.norm_of_nonneg (Nat.cast_nonneg _), Real.norm_of_nonneg (by positivity)] at hcount
  have hmain : (almostPrimeCounting k x : ℝ) ≤
      (x : ℝ) * Real.log x ^ (1 / 4 : ℝ) / Real.log x := by
    refine hcount.trans ?_
    rw [← mul_div_assoc, mul_left_comm C]
    exact div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left hnum (Nat.cast_nonneg _))
      hL (le_mul_of_one_le_left hL.le hfac)
  calc
    _ ≤ ((x : ℝ) * Real.log x ^ (1 / 4 : ℝ) / Real.log x) *
        Real.log x ^ (3 / 4 : ℝ) := by gcongr
    _ = x := by
      rw [div_mul_eq_mul_div, mul_assoc, ← Real.rpow_add hL]
      norm_num [hL.ne']

private lemma enum_growth {k : ℕ} (hk : 1 ≤ k) :
    ∀ᶠ n : ℕ in atTop, (n : ℝ) * Real.log n ^ (3 / 4 : ℝ) ≤ enum k n := by
  have hmono := enum_strictMono hk
  filter_upwards [hmono.tendsto_atTop.eventually (count_mul_log_le hk), eventually_ge_atTop 1]
    with n h hn
  rw [count_enum hk] at h
  refine le_trans ?_ h
  have hle : (n : ℝ) ≤ enum k n := by exact_mod_cast hmono.id_le n
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  gcongr

/-- The two outer enumerations give a summable reciprocal sequence, by condensation. -/
private lemma summable_pair {k j : ℕ} (hk : 1 ≤ k) (hj : 1 ≤ j) :
    Summable fun n : ℕ ↦ (1 : ℝ) / enum k (enum j n) := by
  have hm := (enum_strictMono hk).comp (enum_strictMono hj)
  apply (summable_condensed_iff_of_nonneg (fun _ ↦ by positivity) ?_).mp
  · have hgrowth : ∀ᶠ n : ℕ in atTop,
        (n : ℝ) * Real.log n ^ (3 / 2 : ℝ) ≤ enum k (enum j n) := by
      filter_upwards [enum_growth hj,
        (enum_strictMono hj).tendsto_atTop.eventually (enum_growth hk), eventually_ge_atTop 2]
        with n hjn hkn hn
      have hn' : (1 : ℝ) < n := by exact_mod_cast (by omega : 1 < n)
      have hle : (n : ℝ) ≤ enum j n := by exact_mod_cast (enum_strictMono hj).id_le n
      calc
        _ = ((n : ℝ) * Real.log n ^ (3 / 4 : ℝ)) * Real.log n ^ (3 / 4 : ℝ) := by
          rw [mul_assoc, ← Real.rpow_add (Real.log_pos hn')]
          norm_num
        _ ≤ (enum j n : ℝ) * Real.log (enum j n) ^ (3 / 4 : ℝ) := by gcongr
        _ ≤ _ := hkn
    have hp := (Real.summable_one_div_nat_rpow.mpr (by norm_num : (1 : ℝ) < 3 / 2)).mul_right
      ((Real.log 2 ^ (3 / 2 : ℝ))⁻¹)
    apply hp.of_norm_bounded_eventually_nat
    filter_upwards [(tendsto_pow_atTop_atTop_of_one_lt (by decide : 1 < (2 : ℕ))).eventually
      hgrowth, eventually_gt_atTop 0] with m h hmpos
    push_cast at h
    have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hm' : (0 : ℝ) < m := by exact_mod_cast hmpos
    rw [Real.log_pow, Real.mul_rpow hm'.le hlog.le] at h
    rw [Real.norm_of_nonneg (by positivity)]
    calc
      _ ≤ (2 : ℝ) ^ m * (1 / ((2 : ℝ) ^ m *
          ((m : ℝ) ^ (3 / 2 : ℝ) * Real.log 2 ^ (3 / 2 : ℝ)))) := by
        exact mul_le_mul_of_nonneg_left (one_div_le_one_div_of_le (by positivity) h) (by positivity)
      _ = _ := by field_simp
  · intro m n hmpos hmn
    apply one_div_le_one_div_of_le
    · exact_mod_cast hmpos.trans_le (hm.id_le m)
    · exact_mod_cast hm.monotone hmn

/-- Compose the one-based enumerations from the inside out. -/
private noncomputable def enumerate : List ℕ → ℕ → ℕ
  | [] => id
  | k :: ks => enum k ∘ enumerate ks

private lemma enumerate_strictMono {ks : List ℕ} (h : ∀ i ∈ ks, 1 ≤ i) :
    StrictMono (enumerate ks) := by
  induction ks with
  | nil => exact strictMono_id
  | cons k ks ih =>
    simp only [List.forall_mem_cons] at h
    exact (enum_strictMono h.1).comp (ih h.2)

private lemma cons_image {k j : ℕ} {L : List ℕ}
    (h : ∀ i ∈ almostPrimeIndexSet j L, 0 < i) :
    almostPrimeIndexSet k (j :: L) = enum k '' almostPrimeIndexSet j L := by
  ext n
  constructor
  · rintro ⟨_ | i, hi, hpos, heq⟩
    · omega
    · exact ⟨i + 1, hi, heq.symm⟩
  · rintro ⟨_ | i, hi, rfl⟩
    · exact (lt_irrefl _ (h 0 hi)).elim
    · exact ⟨i + 1, hi, Nat.succ_pos _, rfl⟩

private lemma append_eq_image (k r : ℕ) (ks : List ℕ) (h : ∀ i ∈ ks, 1 ≤ i) :
    almostPrimeIndexSet k (ks ++ [r]) = enumerate (k :: ks) '' {n | Nat.IsAlmostPrime r n} := by
  induction ks generalizing k with
  | nil =>
    exact cons_image fun _ hi ↦ Nat.pos_of_ne_zero hi.1
  | cons j ks ih =>
    obtain ⟨hj, hks⟩ := List.forall_mem_cons.mp h
    rw [List.cons_append, cons_image, ih j hks, Set.image_image]
    · rfl
    · intro i hi
      rw [ih j hks] at hi
      obtain ⟨n, hn, rfl⟩ := hi
      exact (Nat.pos_of_ne_zero hn.1).trans_le ((enumerate_strictMono h).id_le _)

/-- Every member of an almost prime index set with outer factor count `j` is a value of the
one-based enumeration of the `j`-almost primes. -/
private lemma subset_range_enum (j : ℕ) (js : List ℕ) :
    almostPrimeIndexSet j js ⊆ Set.range (enum j) := by
  cases js with
  | nil =>
    intro i hi
    exact ⟨Nat.count (Nat.IsAlmostPrime j) i + 1, Nat.nth_count hi⟩
  | cons j' js' =>
    rintro i ⟨i', -, hi', rfl⟩
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hi'
    exact ⟨m + 1, rfl⟩

end AlmostPrimeIndex

open AlmostPrimeIndex

/-- **Convergence of reciprocal sums over almost primes of almost prime index.** A $k$-almost
prime is a positive integer with exactly $k$ prime factors counted with multiplicity. For positive
integers $k_1, \dots, k_m$ let $N_{k_1}$ be the set of $k_1$-almost primes and, for $m \ge 2$, let
$N_{k_1 k_2 \cdots k_m}$ be the set of $k_1$-almost primes whose index in the increasing
enumeration of the $k_1$-almost primes (starting at $1$) lies in $N_{k_2 \cdots k_m}$. Then for
every $m \ge 2$ and all positive integers $k_1, \dots, k_m$ the series
$\sum_{n \in N_{k_1 k_2 \cdots k_m}} 1/n$ converges.

In particular (the case $m = 2$), for all positive integers $j$ and $k$ the sum of the reciprocals
of the $j$-almost primes of $k$-almost prime index converges.

Source: Paul Kinlaw, Megan Triplett, and William Tripp, *Almost Primes of Almost Prime Index*,
INTEGERS 24 (2024), Article A99, Theorem 5 (`integers-2024-A99-thm-5`). -/
public theorem summable_inv_almostPrimeIndexSet {k : ℕ} {L : List ℕ} (hk : 1 ≤ k)
    (hL : L ≠ []) (hpos : ∀ j ∈ L, 1 ≤ j) :
    Summable fun n : almostPrimeIndexSet k L => (1 : ℝ) / n := by
  obtain ⟨j, js, rfl⟩ := List.exists_cons_of_ne_nil hL
  have hj : 1 ≤ j := hpos j List.mem_cons_self
  -- Only the two outer enumerations matter: `N_{k j ⋯}` lies in the range of `enum k ∘ enum j`.
  have hsub : almostPrimeIndexSet k (j :: js) ⊆ Set.range (enum k ∘ enum j) := by
    rintro n ⟨i, hi, hi1, rfl⟩
    obtain ⟨m, rfl⟩ := subset_range_enum j js hi
    obtain ⟨i', hi'⟩ := Nat.exists_eq_add_of_le' hi1
    refine ⟨m, ?_⟩
    simp only [Function.comp_apply, hi', Nat.add_sub_cancel]
    rfl
  have hrange : Summable fun n : Set.range (enum k ∘ enum j) => (1 : ℝ) / n :=
    (Equiv.ofInjective _ ((enum_strictMono hk).comp (enum_strictMono hj)).injective).summable_iff.mp
      (summable_pair hk hj)
  -- Elaborating without the expected type first keeps unification cheap.
  exact (hrange.comp_injective (Set.inclusion_injective hsub) :)

/-- **Reciprocal sums over iterated almost prime index sets tend to zero.** A $k$-almost prime is
a positive integer with exactly $k$ prime factors counted with multiplicity. For positive integers
$k_1, \dots, k_m$ let $N_{k_1}$ be the set of $k_1$-almost primes and, for $m \ge 2$, let
$N_{k_1 k_2 \cdots k_m}$ be the set of $k_1$-almost primes whose index in the increasing
enumeration of the $k_1$-almost primes (starting at $1$) lies in $N_{k_2 \cdots k_m}$. Fix
$m \ge 2$ and positive integers $k_1, \dots, k_m$. Then
$$
\lim_{k \to \infty} \sum_{n \in N_{k_1 \cdots k_m k}} \frac{1}{n} = 0.
$$

Source: Paul Kinlaw, Megan Triplett, and William Tripp, *Almost Primes of Almost Prime Index*,
INTEGERS 24 (2024), Article A99, Theorem 9, "in particular" clause (`integers-2024-A99-thm-9`). -/
public theorem tendsto_tsum_inv_almostPrimeIndexSet_append_zero {k : ℕ} {ks : List ℕ}
    (hks : ks ≠ []) (hpos : ∀ i ∈ k :: ks, 1 ≤ i) :
    Tendsto (fun k' : ℕ => ∑' n : almostPrimeIndexSet k (ks ++ [k']), (1 : ℝ) / n) atTop (𝓝 0) := by
  obtain ⟨j, js, rfl⟩ := List.exists_cons_of_ne_nil hks
  obtain ⟨hk, hj, hjs⟩ := by simpa only [List.forall_mem_cons] using hpos
  let f (n : ℕ) : ℝ := 1 / enumerate (k :: j :: js) n
  have hf : Summable f :=
    (summable_pair hk hj).comp_injective (enumerate_strictMono hjs).injective
  -- Group the convergent series by the factor count of the innermost index.
  let S (r : ℕ) := {n : ℕ | ArithmeticFunction.cardFactors n = r}
  have hpart (n : ℕ) : ∃! r, n ∈ S r := ⟨_, rfl, fun _ he ↦ he.symm⟩
  have hlim := ((summable_partition (f := f) (fun n ↦ by dsimp [f]; positivity) hpart).mp
    hf).2.tendsto_atTop_zero
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop 0] with r hr
  have hS : {n | Nat.IsAlmostPrime r n} = S r := by
    ext n
    change (n ≠ 0 ∧ ArithmeticFunction.cardFactors n = r) ↔ _
    exact ⟨And.right, fun hn ↦ ⟨fun heq ↦ hr.ne' (by simpa [heq, S] using hn.symm), hn⟩⟩
  rw [append_eq_image k r _ (List.forall_mem_cons.mpr ⟨hj, hjs⟩), hS,
    tsum_image (fun n : ℕ ↦ (1 : ℝ) / n) (enumerate_strictMono hpos).injective.injOn]

end MetaMathlibExt
