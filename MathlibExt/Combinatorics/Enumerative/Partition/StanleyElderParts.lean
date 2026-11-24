/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Order.BigOperators.Group.Multiset
public import Mathlib.Combinatorics.Enumerative.Partition.Basic
public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.RingTheory.PowerSeries.PiTopology
public import Mathlib.Topology.Instances.Rat
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Tactic.Ring
import MathlibExt.Combinatorics.Enumerative.Partition.Counting

/-!
# Stanley's theorem and parts of n-color partitions

We prove Stanley's identity for ordinary partitions. We also enumerate partitions in which
each size has as many colors as its value and prove the generating function for the total
number of even-sized parts, counted with multiplicity, and for the number of distinct colored
parts occurring at least a given number of times.
-/

open PowerSeries
open scoped PowerSeries.WithPiTopology

namespace MetaMathlibExt

open Finset in
/-- **Stanley's theorem.** For every natural number $n$, the total number of parts equal to $1$,
counted with multiplicity, over all partitions of $n$ equals the sum, over all partitions
$\lambda$ of $n$, of the number of distinct parts of $\lambda$.

Source: Shruti Sharma and Amandeep Kaur, *Enumerating Parts of n-Color Partitions*,
INTEGERS 25 (2025), Article A94, Theorem 1 (Stanley's theorem). -/
public theorem sum_count_one_eq_sum_card_toFinset (n : ℕ) :
    ∑ p : Nat.Partition n, p.parts.count 1 = ∑ p : Nat.Partition n, p.parts.toFinset.card := by
  have ones (p : Nat.Partition n) :
      ((Icc 1 n).filter (· ≤ p.parts.count 1)).card = p.parts.count 1 := by
    have hcard : p.parts.card ≤ n := by
      simpa [p.parts_sum] using
        (Multiset.card_nsmul_le_sum (a := (1 : ℕ)) fun _ hi => p.parts_pos hi)
    have hcount := (Multiset.count_le_card 1 p.parts).trans hcard
    have h : (Icc 1 n).filter (· ≤ p.parts.count 1) = Icc 1 (p.parts.count 1) := by
      ext m
      simp only [mem_filter, mem_Icc]
      exact ⟨fun hm => ⟨hm.1.1, hm.2⟩, fun hm => ⟨⟨hm.1, hm.2.trans hcount⟩, hm.2⟩⟩
    rw [h, Nat.card_Icc, Nat.add_sub_cancel]
  have distinctParts (p : Nat.Partition n) :
      (Icc 1 n).filter (· ∈ p.parts) = p.parts.toFinset := by
    ext m
    simp only [mem_filter, mem_Icc, Multiset.mem_toFinset]
    exact ⟨And.right, fun hm => ⟨⟨p.parts_pos hm, p.le_of_mem_parts hm⟩, hm⟩⟩
  have countBySize (P : Nat.Partition n → ℕ → Prop) [DecidableRel P] :
      (∑ p : Nat.Partition n, ((Icc 1 n).filter (P p)).card) =
        ∑ m ∈ Icc 1 n, Fintype.card {p : Nat.Partition n // P p m} := by
    simp only [Fintype.card_subtype, card_eq_sum_ones, sum_filter]
    exact sum_comm
  calc
    _ = ∑ p : Nat.Partition n, ((Icc 1 n).filter (· ≤ p.parts.count 1)).card := by
      simp only [ones]
    _ = ∑ m ∈ Icc 1 n, Fintype.card {p : Nat.Partition n // m ≤ p.parts.count 1} :=
      countBySize _
    _ = ∑ m ∈ Icc 1 n, Fintype.card {p : Nat.Partition n // m ∈ p.parts} := by
      refine sum_congr rfl fun m hm => ?_
      obtain ⟨hm₁, hmn⟩ := mem_Icc.mp hm
      -- Remove `m` ones on the left and one part of size `m` on the right.
      calc
        _ = Fintype.card (Nat.Partition (n - m)) := by
          simpa only [mul_one] using
            (Nat.Partition.card_count_ge (v := 1) (k := m) (by decide)
              (by simpa only [mul_one] using hmn))
        _ = _ := (Fintype.card_congr (Nat.Partition.partitionWithPartEquiv hm₁ hmn)).symm
    _ = ∑ p : Nat.Partition n, ((Icc 1 n).filter (· ∈ p.parts)).card :=
      (countBySize _).symm
    _ = _ := by simp only [distinctParts]

@[expose] public section

/-! ### `n`-color partitions

An `n`-color partition (Agarwal and Andrews) of `m` is a partition of `m` in which a part of
size `k` comes in `k` colors `k_1, …, k_k`. It is encoded as a multiset of colored parts
`(k, j)` with `1 ≤ j ≤ k`, whose sizes `k` sum to `m`; "distinct" means no colored part
repeats, "odd parts" means every size `k` is odd, and the number of parts counts colored parts
with multiplicity. -/

/-- **The list of colored parts of size at most $m$.** For $m \ge 0$, this is the list of the
colored parts $k_j$, that is, the pairs $(k, j)$ of natural numbers with $1 \le j \le k \le m$,
each listed once, in the order $1_1, 2_1, 2_2, 3_1, 3_2, 3_3, \dots$ (by size $k$, then by
color $j$).

Source: Shruti Sharma and Amandeep Kaur, *Enumerating Parts of n-Color Partitions*,
INTEGERS 25 (2025), Article A94, Section 1 (`n`-color partitions). -/
public def nColorPartsUpTo (m : ℕ) : List (ℕ × ℕ) :=
  (List.range m).flatMap fun k => (List.range (k + 1)).map fun j => (k + 1, j + 1)

/-- **Membership in the colored parts of bounded size.** For all natural numbers $m$, $k$ and
$j$, the pair $(k, j)$ appears in the list of colored parts of size at most $m$ if and only if
$1 \le j \le k \le m$.

Source: Shruti Sharma and Amandeep Kaur, *Enumerating Parts of n-Color Partitions*,
INTEGERS 25 (2025), Article A94, Section 1 (`n`-color partitions). -/
public theorem mem_nColorPartsUpTo (m : ℕ) (x : ℕ × ℕ) :
    x ∈ nColorPartsUpTo m ↔ 1 ≤ x.2 ∧ x.2 ≤ x.1 ∧ x.1 ≤ m := by
  obtain ⟨k, j⟩ := x
  simp only [nColorPartsUpTo, List.mem_flatMap, List.mem_range, List.mem_map, Prod.mk.injEq]
  constructor
  · rintro ⟨a, ha, b, hb, rfl, rfl⟩; omega
  · rintro ⟨h1, h2, h3⟩; exact ⟨k - 1, by omega, j - 1, by omega, by omega, by omega⟩

/-- **Multisets of parts with a given size sum.** For a list $L$ of pairs of natural numbers, where
the size of a pair $(k, j)$ is $k$, and a natural number $n$, this is the finite set of multisets
of pairs defined by recursion on $L$. For the empty list it is the set containing only the empty
multiset when $n = 0$, and the empty set otherwise. For a list with head $c$ of size $k$ and tail
$L'$, it is the set of all multisets obtained by adding $i$ copies of $c$ to a member of the set
for $L'$ and $n - ik$, where $i$ ranges over the natural numbers with $i \le n$ and $ik \le n$.

When every pair in $L$ has positive size, this is exactly the set of multisets whose elements all
lie in $L$ and whose sizes, counted with multiplicity, sum to $n$.

Source: Shruti Sharma and Amandeep Kaur, *Enumerating Parts of n-Color Partitions*,
INTEGERS 25 (2025), Article A94, Section 1 (`n`-color partitions; helper for `C(m)`). -/
public def multisetsWithSizeSum : List (ℕ × ℕ) → ℕ → Finset (Multiset (ℕ × ℕ))
  | [], n => if n = 0 then {0} else ∅
  | c :: cs, n => (Finset.range (n + 1)).biUnion fun i =>
      if i * c.1 ≤ n then
        (multisetsWithSizeSum cs (n - i * c.1)).image (Multiset.replicate i c + ·)
      else ∅

/-- **Membership in the multisets with a given size sum.** Let $L$ be a list of pairs of natural
numbers in which every pair $(k, j)$ has size $k \ge 1$, and let $n$ be a natural number. A
multiset $s$ of pairs belongs to the set of multisets drawn from $L$ with size sum $n$ if and only
if every element of $s$ lies in $L$ and the sizes of the elements of $s$, counted with
multiplicity, sum to $n$.

Source: Shruti Sharma and Amandeep Kaur, *Enumerating Parts of n-Color Partitions*,
INTEGERS 25 (2025), Article A94, Section 1 (`n`-color partitions; helper for `C(m)`). -/
public theorem mem_multisetsWithSizeSum (L : List (ℕ × ℕ)) (hL : ∀ c ∈ L, 1 ≤ c.1) (n : ℕ)
    (s : Multiset (ℕ × ℕ)) :
    s ∈ multisetsWithSizeSum L n ↔ (∀ x ∈ s, x ∈ L) ∧ (s.map Prod.fst).sum = n := by
  induction L generalizing n s with
  | nil =>
    simp only [multisetsWithSizeSum, List.not_mem_nil, imp_false]
    by_cases hn : n = 0
    · subst hn
      simp only [ite_true, Finset.mem_singleton]
      constructor
      · rintro rfl; simp
      · rintro ⟨h, -⟩; exact Multiset.eq_zero_iff_forall_notMem.mpr h
    · simp only [hn, ite_false, Finset.notMem_empty, false_iff, not_and]
      intro h
      rw [Multiset.eq_zero_iff_forall_notMem.mpr h]
      simpa using Ne.symm hn
  | cons c cs ih =>
    have hc : 1 ≤ c.1 := hL c (by simp)
    have hcs : ∀ d ∈ cs, 1 ≤ d.1 := fun d hd => hL d (by simp [hd])
    simp only [multisetsWithSizeSum, Finset.mem_biUnion, Finset.mem_range]
    constructor
    · rintro ⟨i, -, hs⟩
      split_ifs at hs with hi
      · obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hs
        obtain ⟨htm, hts⟩ := (ih hcs _ t).mp ht
        refine ⟨fun x hx => ?_, ?_⟩
        · rcases Multiset.mem_add.mp hx with hx | hx
          · simp [Multiset.eq_of_mem_replicate hx]
          · simp [htm x hx]
        · simp [Multiset.map_replicate, Multiset.sum_replicate, hts]
          omega
      · simp at hs
    · rintro ⟨hmem, hsum⟩
      set i := s.count c
      set t := s.filter (· ≠ c)
      have hsplit : s = Multiset.replicate i c + t := by
        rw [← Multiset.filter_add_not (· = c) s, Multiset.filter_eq' s c]
      have hsum' : i * c.1 + (t.map Prod.fst).sum = n := by
        rw [← hsum]; conv_rhs => rw [hsplit]
        simp [Multiset.map_replicate, Multiset.sum_replicate]
      have htmem : ∀ x ∈ t, x ∈ cs := by
        intro x hx
        obtain ⟨hxs, hxc⟩ := Multiset.mem_filter.mp hx
        rcases List.mem_cons.mp (hmem x hxs) with h | h
        · exact absurd h hxc
        · exact h
      refine ⟨i, ?_, ?_⟩
      · have : i ≤ i * c.1 := Nat.le_mul_of_pos_right i hc
        omega
      · split_ifs with hi
        · exact Finset.mem_image.mpr ⟨t, (ih hcs _ t).mpr ⟨htmem, by omega⟩, hsplit.symm⟩
        · omega

/-- **n-color partitions.** For a natural number $m$, the $n$-color partitions of $m$ form the
finite set of multisets of colored parts $k_j$, that is pairs $(k, j)$ of natural numbers with
$1 \le j \le k$ (a part of size $k$ comes in $k$ colors), whose sizes $k$, counted with
multiplicity, sum to $m$.

Source: Shruti Sharma and Amandeep Kaur, *Enumerating Parts of n-Color Partitions*,
INTEGERS 25 (2025), Article A94, Section 1 (`n`-color partitions; `C(m)` is their number). -/
public def nColorPartitions (m : ℕ) : Finset (Multiset (ℕ × ℕ)) :=
  multisetsWithSizeSum (nColorPartsUpTo m) m

/-- **Characterization of $n$-color partitions.** For every natural number $m$, a multiset $s$ of
pairs of natural numbers is an $n$-color partition of $m$ if and only if every element $(k, j)$ of
$s$ satisfies $1 \le j \le k$ and the sizes $k$ of the elements of $s$, counted with
multiplicity, sum to $m$.

Source: Shruti Sharma and Amandeep Kaur, *Enumerating Parts of n-Color Partitions*,
INTEGERS 25 (2025), Article A94, Section 1 (`n`-color partitions). -/
public theorem mem_nColorPartitions (m : ℕ) (s : Multiset (ℕ × ℕ)) :
    s ∈ nColorPartitions m ↔ (∀ x ∈ s, 1 ≤ x.2 ∧ x.2 ≤ x.1) ∧ (s.map Prod.fst).sum = m := by
  rw [nColorPartitions, mem_multisetsWithSizeSum _ (fun c hc => by
    have := (mem_nColorPartsUpTo m c).mp hc; omega)]
  simp only [mem_nColorPartsUpTo]
  constructor
  · rintro ⟨h, hs⟩; exact ⟨fun x hx => ⟨(h x hx).1, (h x hx).2.1⟩, hs⟩
  · rintro ⟨h, hs⟩
    refine ⟨fun x hx => ⟨(h x hx).1, (h x hx).2, ?_⟩, hs⟩
    rw [← hs]
    exact Multiset.le_sum_of_mem (Multiset.mem_map_of_mem Prod.fst hx)

/-- **Small values of the number of n-color partitions.** Let $C(m)$ be the number of $n$-color
partitions of $m$, and write $k_j$ for the colored part of size $k$ and color $j$. Then
$C(0) = C(1) = 1$, $C(2) = 3$ and $C(3) = 6$, and the $n$-color partitions of $2$ are exactly
$2_1$, $2_2$ and $1_1 + 1_1$.

Source: Shruti Sharma and Amandeep Kaur, *Enumerating Parts of n-Color Partitions*,
INTEGERS 25 (2025), Article A94, Section 1 (`C(m)`, generating function
`∏_{m ≥ 1} (1 - q^m)^{-m}`). -/
public theorem nColorPartitions_card_small :
    (nColorPartitions 0).card = 1 ∧ (nColorPartitions 1).card = 1 ∧
      (nColorPartitions 2).card = 3 ∧ (nColorPartitions 3).card = 6 ∧
      nColorPartitions 2 = {{(1, 1), (1, 1)}, {(2, 1)}, {(2, 2)}} := by
  decide +kernel

/-- **Sum of odd divisors.** For a natural number $k$, $\sigma_{\mathrm{odd}}(k)$ is the sum of
the odd positive divisors of $k$. By convention $\sigma_{\mathrm{odd}}(0) = 0$.

Source: Shruti Sharma and Amandeep Kaur, *Enumerating Parts of n-Color Partitions*,
INTEGERS 25 (2025), Article A94, Corollaries 2, 4, 7, 10, 12 (`σ_odd`). -/
public def sigmaOdd (k : ℕ) : ℕ := ∑ d ∈ k.divisors.filter Odd, d

/-- **Sum of the even divisors.** For a natural number $k$, $\sigma_{\mathrm{even}}(k)$ is the
sum of the even divisors of $k$ (so $\sigma_{\mathrm{even}}(0) = 0$).

Source: Shruti Sharma and Amandeep Kaur, *Enumerating Parts of n-Color Partitions*,
INTEGERS 25 (2025), Article A94, Corollary 3 (`σ_even`). -/
public def sigmaEven (k : ℕ) : ℕ := ∑ d ∈ k.divisors.filter Even, d

/-- **Odd and even divisor sums of 12 and 9.** The sums of the odd and of the even divisors
of $12$ and $9$ are $\sigma_{\mathrm{odd}}(12) = 1 + 3 = 4$,
$\sigma_{\mathrm{even}}(12) = 2 + 4 + 6 + 12 = 24$, $\sigma_{\mathrm{odd}}(9) = 1 + 3 + 9 = 13$
and $\sigma_{\mathrm{even}}(9) = 0$.

Source: Shruti Sharma and Amandeep Kaur, *Enumerating Parts of n-Color Partitions*,
INTEGERS 25 (2025), Article A94, Corollaries 3 and 4. -/
public theorem sigmaOdd_sigmaEven_small :
    sigmaOdd 12 = 4 ∧ sigmaEven 12 = 24 ∧ sigmaOdd 9 = 13 ∧ sigmaEven 9 = 0 := by
  decide

end

namespace nColor_evenParts_generatingFunction

open Finset Filter PowerSeries.WithPiTopology
open scoped Topology

private noncomputable def bounded (S : Finset (ℕ × ℕ)) (n : ℕ) :=
  multisetsWithSizeSum S.toList n

private lemma mem_bounded {S : Finset (ℕ × ℕ)} (hS : ∀ c ∈ S, 0 < c.1) (n : ℕ)
    (s : Multiset (ℕ × ℕ)) :
    s ∈ bounded S n ↔ (∀ c ∈ s, c ∈ S) ∧ (s.map Prod.fst).sum = n := by
  simpa [bounded] using
    mem_multisetsWithSizeSum S.toList (fun p hp => hS p (Finset.mem_toList.mp hp)) n s

private noncomputable def series (S : Finset (ℕ × ℕ)) (f : Multiset (ℕ × ℕ) → ℚ) : ℚ⟦X⟧ :=
  PowerSeries.mk fun n => ∑ s ∈ bounded S n, f s

/-- Removing one copy of the new color accounts for all partitions using it. -/
private lemma series_insert {S : Finset (ℕ × ℕ)} {c : ℕ × ℕ}
    (hc : c ∉ S) (hpos : ∀ p ∈ insert c S, 0 < p.1) (f : Multiset (ℕ × ℕ) → ℚ) :
    series (insert c S) f = series S f +
      X ^ c.1 * series (insert c S) (fun s => f (c ::ₘ s)) := by
  classical
  ext n
  rw [map_add, coeff_X_pow_mul']
  simp only [series, coeff_mk]
  have hS : ∀ p ∈ S, 0 < p.1 := fun p hp => hpos p (mem_insert_of_mem hp)
  have without : (bounded (insert c S) n).filter (fun s => c ∉ s) = bounded S n := by
    ext s
    simp only [mem_filter, mem_bounded hpos, mem_bounded hS, mem_insert]
    grind
  have partitionSum := sum_filter_add_sum_filter_not (bounded (insert c S) n) (fun s => c ∈ s) f
  rw [without, add_comm] at partitionSum
  rw [← partitionSum]
  congr 1
  by_cases hn : c.1 ≤ n
  · simp only [hn, ↓reduceIte]
    let addCopy : Multiset (ℕ × ℕ) ↪ Multiset (ℕ × ℕ) :=
      ⟨Multiset.cons c, fun _ _ => (Multiset.cons_inj_right c).mp⟩
    have keep : (bounded (insert c S) n).filter (fun s => c ∈ s) =
        (bounded (insert c S) (n - c.1)).map addCopy := by
      ext s
      simp only [mem_filter, Finset.mem_map, mem_bounded hpos]
      constructor
      · rintro ⟨⟨hall, hsum⟩, hmem⟩
        obtain ⟨t, rfl⟩ := Multiset.exists_cons_of_mem hmem
        simp only [Multiset.forall_mem_cons, Multiset.map_cons, Multiset.sum_cons] at hall hsum
        exact ⟨t, ⟨hall.2, by omega⟩, rfl⟩
      · rintro ⟨t, ⟨hall, hsum⟩, rfl⟩
        change ((∀ p ∈ c ::ₘ t, p ∈ insert c S) ∧ _) ∧ c ∈ c ::ₘ t
        refine ⟨⟨Multiset.forall_mem_cons.mpr ⟨mem_insert_self .., hall⟩, ?_⟩,
          Multiset.mem_cons_self ..⟩
        change ((c ::ₘ t).map Prod.fst).sum = n
        simp [hsum, Nat.add_sub_of_le hn]
    rw [keep, sum_map]
    rfl
  · simp only [hn, ↓reduceIte]
    apply sum_eq_zero
    intro s hs
    obtain ⟨hs, hcs⟩ := mem_filter.mp hs
    have hle := Multiset.le_sum_of_mem (Multiset.mem_map_of_mem Prod.fst hcs)
    rw [((mem_bounded hpos n s).mp hs).2] at hle
    exact (hn hle).elim

private def evenCount (s : Multiset (ℕ × ℕ)) : ℚ := (s.filter fun c => Even c.1).card

private noncomputable def term (k : ℕ) : ℚ⟦X⟧ := X ^ k * (1 - X ^ k)⁻¹

/-- The finite Euler product cancels the counting series. For the series weighted by
even-part multiplicity, one geometric contribution survives for each even color. -/
private lemma finite_identity (S : Finset (ℕ × ℕ)) (hS : ∀ c ∈ S, 0 < c.1) :
    (∏ c ∈ S, (1 - X ^ c.1 : ℚ⟦X⟧)) * series S (fun _ => 1) = 1 ∧
      (∏ c ∈ S, (1 - X ^ c.1 : ℚ⟦X⟧)) * series S evenCount =
        ∑ c ∈ S, if Even c.1 then term c.1 else 0 := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    simp only [prod_empty, one_mul, sum_empty]
    constructor <;> ext n <;> cases n <;>
      simp [series, bounded, multisetsWithSizeSum, evenCount]
  | @insert c S hc ih =>
    obtain ⟨count, marked⟩ := ih (fun p hp => hS p (mem_insert_of_mem hp))
    let D := ∏ p ∈ S, (1 - X ^ p.1 : ℚ⟦X⟧)
    let x : ℚ⟦X⟧ := X ^ c.1
    have recCount := series_insert hc hS (fun _ => 1)
    have unmark : (1 - x) * series (insert c S) (fun _ => 1) = series S (fun _ => 1) := by
      linear_combination recCount
    rw [prod_insert hc, sum_insert hc]
    change (1 - x) * D * _ = 1 ∧ (1 - x) * D * _ = _
    have count' : (1 - x) * D * series (insert c S) (fun _ => 1) = 1 := by
      rwa [mul_right_comm, unmark, mul_comm]
    refine ⟨count', ?_⟩
    have recMarked := series_insert hc hS evenCount
    by_cases he : Even c.1
    · have addOne : series (insert c S) (fun s => evenCount (c ::ₘ s)) =
          series (insert c S) evenCount + series (insert c S) (fun _ => 1) := by
        ext n
        simp [series, evenCount, he, sum_add_distrib]
      rw [addOne] at recMarked
      have inv : (1 - x)⁻¹ * (1 - x) = 1 := by
        apply PowerSeries.inv_mul_cancel
        have hk := hS c (mem_insert_self ..)
        simp [x, Nat.ne_of_gt hk]
      simp only [he, ↓reduceIte]
      rw [← marked]
      change (1 - x) * D * _ = x * (1 - x)⁻¹ + D * _
      linear_combination D * recMarked + x * (1 - x)⁻¹ * count' -
        x * D * series (insert c S) (fun _ => 1) * inv
    · have same : (fun s => evenCount (c ::ₘ s)) = evenCount := by
        funext s
        simp [evenCount, he]
      rw [same] at recMarked
      simp only [he, ↓reduceIte, zero_add]
      rw [← marked]
      change (1 - x) * D * _ = D * _
      linear_combination D * recMarked

/-- The colors of size `i + 1`, indexed by their second component. -/
private def color (i : ℕ) : ℕ ↪ ℕ × ℕ :=
  ⟨fun j => (i + 1, j + 1), fun _ _ h => by simpa using h⟩

private lemma color_apply (i j : ℕ) : color i j = (i + 1, j + 1) := rfl

private def colors (i : ℕ) : Finset (ℕ × ℕ) := (range (i + 1)).map (color i)

private def palette (N : ℕ) := (range N).biUnion colors

private lemma mem_palette {c : ℕ × ℕ} {N : ℕ} :
    c ∈ palette N ↔ 1 ≤ c.2 ∧ c.2 ≤ c.1 ∧ c.1 ≤ N := by
  rw [← mem_nColorPartsUpTo]
  simp [palette, colors, color_apply, nColorPartsUpTo]

private lemma disjoint_colors {i j : ℕ} (h : i ≠ j) : Disjoint (colors i) (colors j) := by
  rw [Finset.disjoint_left]
  intro c hi hj
  obtain ⟨a, _, rfl⟩ := Finset.mem_map.mp hi
  obtain ⟨b, _, he⟩ := Finset.mem_map.mp hj
  change (j + 1, b + 1) = (i + 1, a + 1) at he
  exact h (by simpa using congrArg Prod.fst he.symm)

private noncomputable def factor (i : ℕ) : ℚ⟦X⟧ := (1 - X ^ (i + 1)) ^ (i + 1)

private noncomputable def summand (i : ℕ) : ℚ⟦X⟧ :=
  (2 * (i + 1) : ℕ) * term (2 * (i + 1))

private lemma sum_even_sizes (N : ℕ) :
    (∑ i ∈ range (2 * N), (i + 1) • (if Even (i + 1) then term (i + 1) else 0)) =
      ∑ i ∈ range N, summand i := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Nat.mul_succ, sum_range_succ, sum_range_succ, ih, sum_range_succ]
    have oddSize : ¬ Even (2 * N + 1) := by simp
    have evenSize : Even (2 * N + 1 + 1) := ⟨N + 1, by omega⟩
    simp only [oddSize, evenSize, ↓reduceIte, mul_zero, add_zero, summand,
      show 2 * (N + 1) = 2 * N + 1 + 1 by omega, nsmul_eq_mul]

private lemma bounded_identity (N : ℕ) :
    (∏ i ∈ range (2 * N), factor i) * series (palette (2 * N)) evenCount =
      ∑ i ∈ range N, summand i := by
  have h := (finite_identity (palette (2 * N)) fun p hp => by
    have := mem_palette.mp hp
    omega).2
  have hd : (range (2 * N) : Set ℕ).PairwiseDisjoint colors :=
    fun _ _ _ _ hij => disjoint_colors hij
  rw [← sum_even_sizes]
  simp only [palette, prod_biUnion hd, sum_biUnion hd, colors, prod_map, sum_map,
    color_apply, prod_const, card_range] at h
  refine h.trans (sum_congr rfl fun i _ => ?_)
  change (∑ _j ∈ range (i + 1), if Even (i + 1) then term (i + 1) else 0) = _
  rw [sum_const, card_range]

/-- Every part has size at most the total, so colors above that bound have no effect. -/
private lemma bounded_stable {n N : ℕ} (h : n ≤ N) :
    bounded (palette N) n = nColorPartitions n := by
  ext s
  rw [mem_bounded (fun p hp => by have := mem_palette.mp hp; omega), mem_nColorPartitions]
  simp only [mem_palette]
  constructor
  · rintro ⟨hall, hsum⟩
    exact ⟨fun p hp => ⟨(hall p hp).1, (hall p hp).2.1⟩, hsum⟩
  · rintro ⟨hall, hsum⟩
    refine ⟨fun p hp => ⟨(hall p hp).1, (hall p hp).2, ?_⟩, hsum⟩
    exact (Multiset.le_sum_of_mem (Multiset.mem_map_of_mem Prod.fst hp)).trans (hsum.le.trans h)

private lemma summable_summand : Summable summand := by
  apply summable_of_tendsto_order_atTop_nhds_top
  apply ENat.tendsto_nhds_top_iff_natCast_lt.mpr
  intro n
  filter_upwards [eventually_ge_atTop n] with i hi
  have h : (n : ℕ∞) < ((2 * (i + 1) : ℕ) : ℕ∞) := by exact_mod_cast (by omega : n < 2 * (i + 1))
  apply h.trans_le
  rw [summand, term, order_mul, order_mul, order_X_pow]
  exact le_self_add.trans le_add_self

private lemma multipliable_factor : Multipliable factor := by
  have heq : factor = fun i => 1 + (factor i - 1) := by ext1 i; ring
  rw [heq]
  apply multipliable_one_add_of_tendsto_order_atTop_nhds_top
  apply ENat.tendsto_nhds_top_iff_natCast_lt.mpr
  intro n
  filter_upwards [eventually_ge_atTop n] with i hi
  obtain ⟨g, hg⟩ := sub_one_dvd_pow_sub_one (1 - X ^ (i + 1) : ℚ⟦X⟧) (i + 1)
  change (n : ℕ∞) < ((1 - X ^ (i + 1) : ℚ⟦X⟧) ^ (i + 1) - 1).order
  rw [hg, show (1 - X ^ (i + 1) : ℚ⟦X⟧) - 1 = -X ^ (i + 1) by ring,
    order_mul, order_neg, order_X_pow]
  exact lt_of_lt_of_le (by exact_mod_cast (by omega : n < i + 1)) le_self_add

end nColor_evenParts_generatingFunction

open nColor_evenParts_generatingFunction Filter PowerSeries.WithPiTopology
open scoped Topology

/-- **Generating function for the even parts of $n$-color partitions.** Let $A_e(m)$ be the total
number of parts of even size, counted with multiplicity, over the $n$-color partitions of $m$.
Then, as formal power series in $q$ over $\mathbb{Q}$, with infinite sums and products taken
coefficientwise,
$$
\sum_{m \ge 1} \frac{2m \, q^{2m}}{1 - q^{2m}} =
\Big(\prod_{m \ge 1} (1 - q^m)^m\Big) \sum_{m \ge 0} A_e(m) \, q^m.
$$

Source: Shruti Sharma and Amandeep Kaur, *Enumerating Parts of n-Color Partitions*,
INTEGERS 25 (2025), Article A94, Theorem 4 (`integers-2025-A94-thm-4`). -/
public theorem nColor_evenParts_generatingFunction :
    ∑' m : ℕ, ((2 * (m + 1) : ℕ) : ℚ⟦X⟧) * X ^ (2 * (m + 1)) * (1 - X ^ (2 * (m + 1)))⁻¹ =
      (∏' m : ℕ, (1 - X ^ (m + 1)) ^ (m + 1) : ℚ⟦X⟧) *
        PowerSeries.mk fun n =>
          ((∑ s ∈ nColorPartitions n, (s.filter fun p => Even p.1).card : ℕ) : ℚ) := by
  have growth : Tendsto (fun N : ℕ => 2 * N) atTop atTop :=
    tendsto_atTop_mono (fun n => by change n ≤ 2 * n; omega) tendsto_id
  have marked : Tendsto (fun N => series (palette (2 * N)) evenCount) atTop
      (𝓝 (PowerSeries.mk fun n => ∑ s ∈ nColorPartitions n, evenCount s)) := by
    apply (tendsto_iff_coeff_tendsto ..).mpr
    intro n
    apply tendsto_atTop_of_eventually_const (i₀ := n)
    intro N hN
    simp [series, bounded_stable (show n ≤ 2 * N by omega)]
  have limit := (multipliable_factor.tendsto_prod_tprod_nat.comp growth).mul marked
  have sums := summable_summand.hasSum.tendsto_sum_nat
  have heq := tendsto_nhds_unique sums (limit.congr fun N => bounded_identity N)
  simpa [summand, factor, term, mul_assoc, evenCount] using heq

namespace nColor_partsMultiplicityGe_generatingFunction

open Finset

private def markedCount (t : ℕ) (s : Multiset (ℕ × ℕ)) : ℚ :=
  (s.toFinset.filter fun p => t ≤ s.count p).card

/-- Removing the marked copies of a fixed color shifts its series by their total size. -/
private lemma series_mark_color (S : Finset (ℕ × ℕ)) (hS : ∀ p ∈ S, 0 < p.1)
    {c : ℕ × ℕ} (hc : c ∈ S) (t : ℕ) :
    series S (fun s => if t ≤ s.count c then 1 else 0) =
      X ^ (c.1 * t) * series S (fun _ => 1) := by
  classical
  ext n
  rw [coeff_X_pow_mul']
  simp only [series, coeff_mk, sum_boole, sum_const, nsmul_one]
  let addCopies : Multiset (ℕ × ℕ) ↪ Multiset (ℕ × ℕ) :=
    ⟨(Multiset.replicate t c + ·), fun _ _ => add_left_cancel⟩
  have weight (r : Multiset (ℕ × ℕ)) :
      ((addCopies r).map Prod.fst).sum = c.1 * t + (r.map Prod.fst).sum := by
    change ((Multiset.replicate t c + r).map Prod.fst).sum = _
    simp [Multiset.map_replicate, Multiset.sum_replicate, Nat.mul_comm]
  have allowed (r : Multiset (ℕ × ℕ)) :
      (∀ p ∈ addCopies r, p ∈ S) ↔ ∀ p ∈ r, p ∈ S := by
    change (∀ p ∈ Multiset.replicate t c + r, p ∈ S) ↔ _
    constructor
    · exact fun h p hp => h p (Multiset.mem_add.mpr (.inr hp))
    · intro h p hp
      obtain hrep | hr := Multiset.mem_add.mp hp
      · exact (Multiset.eq_of_mem_replicate hrep) ▸ hc
      · exact h p hr
  have decompose (s : Multiset (ℕ × ℕ)) :
      t ≤ s.count c ↔ ∃ r, addCopies r = s := by
    rw [Multiset.le_count_iff_replicate_le, Multiset.le_iff_exists_add]
    exact exists_congr fun _ => eq_comm
  by_cases hn : c.1 * t ≤ n
  · have heq : (bounded S n).filter (fun s => t ≤ s.count c) =
        (bounded S (n - c.1 * t)).map addCopies := by
      ext s
      simp only [mem_filter, Finset.mem_map, mem_bounded hS, decompose]
      constructor
      · rintro ⟨⟨hall, hsum⟩, r, rfl⟩
        rw [weight] at hsum
        exact ⟨r, ⟨(allowed r).mp hall, by omega⟩, rfl⟩
      · rintro ⟨r, ⟨hall, hsum⟩, rfl⟩
        exact ⟨⟨(allowed r).mpr hall, by rw [weight, hsum]; omega⟩, r, rfl⟩
    simp [hn, heq]
  · have heq : (bounded S n).filter (fun s => t ≤ s.count c) = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro s hs
      obtain ⟨hs, hcount⟩ := mem_filter.mp hs
      obtain ⟨r, rfl⟩ := (decompose s).mp hcount
      have hsum := ((mem_bounded hS n _).mp hs).2
      rw [weight] at hsum
      omega
    simp [hn, heq]

/-- Sum over the possible marked colors, then cancel the ordinary partition series. -/
private lemma marked_identity (S : Finset (ℕ × ℕ)) (hS : ∀ p ∈ S, 0 < p.1)
    (t : ℕ) (ht : 1 ≤ t) :
    (∏ c ∈ S, (1 - X ^ c.1 : ℚ⟦X⟧)) * series S (markedCount t) =
      ∑ c ∈ S, X ^ (c.1 * t) := by
  classical
  have split : series S (markedCount t) =
      ∑ c ∈ S, series S (fun s => if t ≤ s.count c then 1 else 0) := by
    ext n
    simp only [series, coeff_mk, map_sum]
    rw [sum_comm]
    apply sum_congr rfl
    intro s hs
    rw [markedCount, sum_boole]
    congr 2
    ext c
    simp only [mem_filter, Multiset.mem_toFinset]
    have hall := ((mem_bounded hS n s).mp hs).1
    exact ⟨fun h => ⟨hall c h.1, h.2⟩, fun h => ⟨Multiset.count_pos.mp (ht.trans h.2), h.2⟩⟩
  rw [split, mul_sum]
  refine sum_congr rfl fun c hc => ?_
  rw [series_mark_color S hS hc, mul_left_comm, (finite_identity S hS).1, mul_one]

private noncomputable def contribution (t i : ℕ) : ℚ⟦X⟧ :=
  ((i + 1 : ℕ) : ℚ⟦X⟧) * X ^ ((i + 1) * t)

private lemma palette_identity (t : ℕ) (ht : 1 ≤ t) (N : ℕ) :
    (∏ i ∈ range N, factor i) * series (palette N) (markedCount t) =
      ∑ i ∈ range N, contribution t i := by
  have h := marked_identity (palette N) (fun p hp => by have := mem_palette.mp hp; omega) t ht
  have hd : (range N : Set ℕ).PairwiseDisjoint colors :=
    fun _ _ _ _ hij => disjoint_colors hij
  simpa only [palette, prod_biUnion hd, sum_biUnion hd, colors, prod_map, sum_map, color_apply,
    prod_const, sum_const, card_range, nsmul_eq_mul, factor, contribution] using h

private lemma summable_contribution (t : ℕ) (ht : 1 ≤ t) : Summable (contribution t) := by
  apply summable_of_tendsto_order_atTop_nhds_top
  apply ENat.tendsto_nhds_top_iff_natCast_lt.mpr
  intro n
  filter_upwards [eventually_ge_atTop n] with i hi
  have h : n < (i + 1) * t := (Nat.lt_succ_of_le hi).trans_le (Nat.le_mul_of_pos_right _ ht)
  rw [contribution, order_mul, order_X_pow]
  exact lt_of_lt_of_le (by exact_mod_cast h) le_add_self

end nColor_partsMultiplicityGe_generatingFunction

open nColor_partsMultiplicityGe_generatingFunction

/-- **Generating function for colored parts of multiplicity at least $t$.** Let $t \ge 1$. For
$m \ge 0$ let $N^t(m)$ be the sum, over all $n$-color partitions of $m$, of the number of
distinct colored parts that occur at least $t$ times. Then, as formal power series in $q$ with
rational coefficients,
$$\sum_{m \ge 1} m q^{mt} = \prod_{m \ge 1} (1 - q^m)^m \sum_{m \ge 0} N^t(m) q^m.$$

Source: Shruti Sharma and Amandeep Kaur, *Enumerating Parts of n-Color Partitions*,
INTEGERS 25 (2025), Article A94, Theorem 6 (`integers-2025-A94-thm-6`). -/
public theorem nColor_partsMultiplicityGe_generatingFunction (t : ℕ) (ht : 1 ≤ t) :
    ∑' m : ℕ, ((m + 1 : ℕ) : ℚ⟦X⟧) * X ^ ((m + 1) * t) =
      (∏' m : ℕ, (1 - X ^ (m + 1)) ^ (m + 1) : ℚ⟦X⟧) *
        PowerSeries.mk fun n =>
          ((∑ s ∈ nColorPartitions n, (s.toFinset.filter fun p => t ≤ s.count p).card : ℕ) :
            ℚ) := by
  have marked : Tendsto (fun N => series (palette N) (markedCount t)) atTop
      (𝓝 (PowerSeries.mk fun n => ∑ s ∈ nColorPartitions n, markedCount t s)) := by
    apply (tendsto_iff_coeff_tendsto ..).mpr
    intro n
    apply tendsto_atTop_of_eventually_const (i₀ := n)
    intro N hN
    simp [series, bounded_stable hN]
  have limit := multipliable_factor.tendsto_prod_tprod_nat.mul marked
  have sums := (summable_contribution t ht).hasSum.tendsto_sum_nat
  have heq := tendsto_nhds_unique sums (limit.congr fun N => palette_identity t ht N)
  simpa [contribution, factor, markedCount] using heq

end MetaMathlibExt
