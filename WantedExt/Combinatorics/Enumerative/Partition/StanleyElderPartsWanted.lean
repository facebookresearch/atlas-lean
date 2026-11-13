/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Combinatorics.Enumerative.Partition.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Multiset
public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.RingTheory.PowerSeries.PiTopology
public import Mathlib.Topology.Instances.Rat

/-!
# Stanley's and Elder's theorems on parts of partitions

The two classical results quoted in the introduction of Shruti Sharma and Amandeep Kaur,
*Enumerating Parts of n-Color Partitions*, INTEGERS 25 (2025), Article A94, and the paper's
`n`-color divisor-sum corollaries whose objects the records define (the rest are listed as
blocked in the audit table).

The paper's generating-function theorems (Theorems 3-12, stated "for `|q| < 1`") are stated as
identities of formal power series in `ℚ⟦X⟧`, with `q = X`, infinite sums and products taken in
the coefficientwise (`PowerSeries.WithPiTopology`) topology and `(1 ∓ q^k)⁻¹` the power-series
inverse.
-/

open PowerSeries
open scoped PowerSeries.WithPiTopology

namespace MetaMathlibExt

@[expose] public section

/-- **Elder's theorem.** Let $n$ and $k$ be natural numbers with $k \ge 1$. The total number of
times the part $k$ occurs, counted with multiplicity, over all partitions of $n$ equals the sum,
over all partitions $\lambda$ of $n$, of the number of distinct parts of $\lambda$ that occur at
least $k$ times in $\lambda$.

The hypothesis $k \ge 1$ is needed: for $k = 0$ and $n = 1$ the left side is $0$ and the right
side is $1$.

Source: Shruti Sharma and Amandeep Kaur, *Enumerating Parts of n-Color Partitions*,
INTEGERS 25 (2025), Article A94, Theorem 2 (Elder's theorem). -/
public theorem_wanted sum_count_eq_sum_card_parts_count_ge (n k : ℕ) (hk : 1 ≤ k) :
    ∑ p : Nat.Partition n, p.parts.count k =
      ∑ p : Nat.Partition n, (p.parts.toFinset.filter fun i => k ≤ p.parts.count i).card

/-- **Stanley's theorem.** For every natural number $n$, the total number of parts equal to $1$,
counted with multiplicity, over all partitions of $n$ equals the sum, over all partitions
$\lambda$ of $n$, of the number of distinct parts of $\lambda$.

Source: Shruti Sharma and Amandeep Kaur, *Enumerating Parts of n-Color Partitions*,
INTEGERS 25 (2025), Article A94, Theorem 1 (Stanley's theorem). -/
public theorem_wanted sum_count_one_eq_sum_card_toFinset (n : ℕ) :
    ∑ p : Nat.Partition n, p.parts.count 1 = ∑ p : Nat.Partition n, p.parts.toFinset.card


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

/-- **Total number of parts of $n$-color partitions via the divisor sum.** For $r \ge 0$ let
$C(r)$ be the number of $n$-color partitions of $r$, and let $T_o(r)$ (resp. $T_e(r)$) be the
total number of parts, counted with multiplicity, over the $n$-color partitions of $r$ having an
odd (resp. even) number of parts. Then for every $m \ge 1$,
$$T_o(m) + T_e(m) = \sum_{k=1}^{m} \sigma(k)\, C(m-k),$$
where $\sigma(k)$ is the sum of the divisors of $k$.

Source: Shruti Sharma and Amandeep Kaur, *Enumerating Parts of n-Color Partitions*,
INTEGERS 25 (2025), Article A94, Corollary 1 (`integers-2025-A94-cor-1`). -/
public theorem_wanted nColor_totalParts_eq_sum_sigma (m : ℕ) (hm : 1 ≤ m) :
    (∑ s ∈ (nColorPartitions m).filter (fun s => Odd s.card), s.card) +
        ∑ s ∈ (nColorPartitions m).filter (fun s => Even s.card), s.card =
      ∑ k ∈ Finset.Icc 1 m, ArithmeticFunction.sigma 1 k * (nColorPartitions (m - k)).card

/-- **Odd-divisor sum via the total number of parts of $n$-color partitions.** For $r \ge 0$
let $T_o(r)$ (resp. $T_e(r)$) be the total number of parts, counted with multiplicity, over the
$n$-color partitions of $r$ having an odd (resp. even) number of parts, and let $C(D, r)$ be the
number of $n$-color partitions of $r$ into distinct colored parts. Then for every $m \ge 1$,
$$\sigma_{\mathrm{odd}}(m) = \sum_{k=1}^{m} \bigl(T_o(k) - T_e(k)\bigr)\, C(D, m-k),$$
where $\sigma_{\mathrm{odd}}(m)$ is the sum of the odd divisors of $m$.

Source: Shruti Sharma and Amandeep Kaur, *Enumerating Parts of n-Color Partitions*,
INTEGERS 25 (2025), Article A94, Corollary 2 (`integers-2025-A94-cor-2`). -/
public theorem_wanted sigmaOdd_eq_sum_nColor_partsDiff_mul_distinct (m : ℕ) (hm : 1 ≤ m) :
    (sigmaOdd m : ℤ) =
      ∑ k ∈ Finset.Icc 1 m,
        (((∑ s ∈ (nColorPartitions k).filter (fun s => Odd s.card), s.card : ℕ) : ℤ) -
            ((∑ s ∈ (nColorPartitions k).filter (fun s => Even s.card), s.card : ℕ) : ℤ)) *
          ((nColorPartitions (m - k)).filter fun s => s.Nodup).card

/-- **Even divisor sums count the even parts of $n$-color partitions.** For $m \ge 1$, let
$A_e(m)$ be the total number of parts of even size, counted with multiplicity, over the
$n$-color partitions of $m$, and for $r \ge 0$ let $C(r)$ be the number of $n$-color partitions
of $r$. Then
$$A_e(m) = \sum_{k=1}^{m} \sigma_{\mathrm{even}}(k) \, C(m - k),$$
where $\sigma_{\mathrm{even}}(k)$ is the sum of the even divisors of $k$.

Source: Shruti Sharma and Amandeep Kaur, *Enumerating Parts of n-Color Partitions*,
INTEGERS 25 (2025), Article A94, Corollary 3 (`integers-2025-A94-cor-3`). -/
public theorem_wanted nColor_evenParts_eq_sum_sigmaEven (m : ℕ) (hm : 1 ≤ m) :
    ∑ s ∈ nColorPartitions m, (s.filter fun p => Even p.1).card =
      ∑ k ∈ Finset.Icc 1 m, sigmaEven k * (nColorPartitions (m - k)).card

/-- **Number of odd parts in n-color partitions as a divisor sum.** For $i \ge 0$ let $A_o(i)$ be
the total number of odd parts (parts of odd size, counted with multiplicity) over the $n$-color
partitions of $i$, and let $C(i)$ be the number of $n$-color partitions of $i$. Then for every
$m \ge 1$,
$$
A_o(m) = \sum_{k=1}^{m} \sigma_{\mathrm{odd}}(k)\, C(m-k),
$$
where $\sigma_{\mathrm{odd}}(k)$ is the sum of the odd divisors of $k$.

Source: Shruti Sharma and Amandeep Kaur, *Enumerating Parts of n-Color Partitions*,
INTEGERS 25 (2025), Article A94, Corollary 4 (`integers-2025-A94-cor-4`). -/
public theorem_wanted nColor_oddParts_eq_sum_sigmaOdd (m : ℕ) (hm : 1 ≤ m) :
    ∑ s ∈ nColorPartitions m, (s.filter fun p => Odd p.1).card =
      ∑ k ∈ Finset.Icc 1 m, sigmaOdd k * (nColorPartitions (m - k)).card

/-- **Parts of multiplicity at least t in n-color partitions.** Let $t \ge 1$. For $i \ge 0$ let
$N^t(i)$ be the number of distinct colored parts occurring at least $t$ times in an $n$-color
partition of $i$, summed over all $n$-color partitions of $i$, and let $C(i)$ be the number of
$n$-color partitions of $i$. Then for every $m \ge t$,
$$
N^t(m) = \sum_{k=1}^{\lfloor m/t \rfloor} k\, C(m - tk).
$$

Source: Shruti Sharma and Amandeep Kaur, *Enumerating Parts of n-Color Partitions*,
INTEGERS 25 (2025), Article A94, Corollary 5 (`integers-2025-A94-cor-5`). -/
public theorem_wanted nColor_partsMultiplicityGe_eq_sum (m t : ℕ) (ht : 1 ≤ t) (htm : t ≤ m) :
    ∑ s ∈ nColorPartitions m, (s.toFinset.filter fun p => t ≤ s.count p).card =
      ∑ k ∈ Finset.Icc 1 (m / t), k * (nColorPartitions (m - t * k)).card

/-- **Parts in a residue class over n-color partitions as a divisor sum.** Let $r$ and $k$ be
natural numbers with $0 < k < r$. For $i \ge 0$ let $C(k \bmod r, i)$ be the total number of
parts of size congruent to $k$ modulo $r$, counted with multiplicity, over the $n$-color
partitions of $i$, and let $C(i)$ be the number of $n$-color partitions of $i$. Then for every
$m \ge 1$,
$$
C(k \bmod r, m) = \sum_{j=1}^{m} \Bigl(\sum_{d \mid j,\ d \equiv k \pmod{r}} d\Bigr) C(m-j).
$$

Source: Shruti Sharma and Amandeep Kaur, *Enumerating Parts of n-Color Partitions*,
INTEGERS 25 (2025), Article A94, Corollary 6 (`integers-2025-A94-cor-6`). -/
public theorem_wanted nColor_partsModEq_eq_sum (m r k : ℕ) (hm : 1 ≤ m) (hk : 0 < k)
    (hkr : k < r) :
    ∑ s ∈ nColorPartitions m, (s.filter fun p => p.1 % r = k).card =
      ∑ j ∈ Finset.Icc 1 m,
        (∑ d ∈ j.divisors.filter (fun d => d % r = k), d) * (nColorPartitions (m - j)).card

/-- **Odd divisor sums count the parts of distinct $n$-color partitions.** Call an $n$-color
partition distinct when no colored part occurs more than once. For $m \ge 1$, let $C_o(D, m)$
(resp. $C_e(D, m)$) be the total number of parts over the distinct $n$-color partitions of $m$
with an odd (resp. even) number of parts, and for $r \ge 0$ let $C(D, r)$ be the number of
distinct $n$-color partitions of $r$. Then
$$C_o(D, m) + C_e(D, m) = \sum_{k=1}^{m} \sigma_{\mathrm{odd}}(k) \, C(D, m - k),$$
where $\sigma_{\mathrm{odd}}(k)$ is the sum of the odd divisors of $k$.

Source: Shruti Sharma and Amandeep Kaur, *Enumerating Parts of n-Color Partitions*,
INTEGERS 25 (2025), Article A94, Corollary 7 (`integers-2025-A94-cor-7`). -/
public theorem_wanted nColor_distinctTotalParts_eq_sum_sigmaOdd (m : ℕ) (hm : 1 ≤ m) :
    (∑ s ∈ (nColorPartitions m).filter (fun s => s.Nodup ∧ Odd s.card), s.card) +
        ∑ s ∈ (nColorPartitions m).filter (fun s => s.Nodup ∧ Even s.card), s.card =
      ∑ k ∈ Finset.Icc 1 m, sigmaOdd k * ((nColorPartitions (m - k)).filter fun s => s.Nodup).card

/-- **Divisor sum via distinct $n$-color partitions.** For $r \ge 0$ let $C(r)$ be the number
of $n$-color partitions of $r$, and let $C_o(D, r)$ (resp. $C_e(D, r)$) be the total number of
parts over the $n$-color partitions of $r$ into an odd (resp. even) number of distinct colored
parts. Then for every $m \ge 1$,
$$\sigma(m) = \sum_{k=1}^{m} \bigl(C_o(D, k) - C_e(D, k)\bigr)\, C(m-k),$$
where $\sigma(m)$ is the sum of the divisors of $m$.

Source: Shruti Sharma and Amandeep Kaur, *Enumerating Parts of n-Color Partitions*,
INTEGERS 25 (2025), Article A94, Corollary 8 (`integers-2025-A94-cor-8`). -/
public theorem_wanted sigma_eq_sum_nColor_distinctPartsDiff (m : ℕ) (hm : 1 ≤ m) :
    (ArithmeticFunction.sigma 1 m : ℤ) =
      ∑ k ∈ Finset.Icc 1 m,
        (((∑ s ∈ (nColorPartitions k).filter (fun s => s.Nodup ∧ Odd s.card), s.card : ℕ) : ℤ) -
            ((∑ s ∈ (nColorPartitions k).filter (fun s => s.Nodup ∧ Even s.card), s.card : ℕ) :
              ℤ)) *
          (nColorPartitions (m - k)).card

/-- **Number of parts in n-color partitions into odd parts as a divisor sum.** For $i \ge 0$ let
$Q(O, i)$ be the total number of parts, counted with multiplicity, over the $n$-color partitions
of $i$ into odd parts (every part has odd size), and let $C(O, i)$ be the number of such
partitions. Then for every $m \ge 1$,
$$
Q(O, m) = \sum_{k=1}^{m} \sigma_{\mathrm{odd}}(k)\, C(O, m-k),
$$
where $\sigma_{\mathrm{odd}}(k)$ is the sum of the odd divisors of $k$.

Source: Shruti Sharma and Amandeep Kaur, *Enumerating Parts of n-Color Partitions*,
INTEGERS 25 (2025), Article A94, Corollary 10 (`integers-2025-A94-cor-10`). -/
public theorem_wanted nColor_oddPartitionParts_eq_sum_sigmaOdd (m : ℕ) (hm : 1 ≤ m) :
    ∑ s ∈ (nColorPartitions m).filter (fun s => ∀ p ∈ s, Odd p.1), s.card =
      ∑ k ∈ Finset.Icc 1 m,
        sigmaOdd k * ((nColorPartitions (m - k)).filter fun s => ∀ p ∈ s, Odd p.1).card

/-- **Odd divisor sums count the parts of $n$-color partitions into odd parts.** Say that an
$n$-color partition has odd parts when every part has odd size. For $m \ge 1$, let $U_o(m)$
(resp. $U_e(m)$) be the total number of parts over the $n$-color partitions of $m$ with odd parts
and an odd (resp. even) number of parts, and for $r \ge 0$ let $C(O, r)$ be the number of
$n$-color partitions of $r$ with odd parts. Then
$$U_o(m) + U_e(m) = \sum_{k=1}^{m} \sigma_{\mathrm{odd}}(k) \, C(O, m - k),$$
where $\sigma_{\mathrm{odd}}(k)$ is the sum of the odd divisors of $k$.

Source: Shruti Sharma and Amandeep Kaur, *Enumerating Parts of n-Color Partitions*,
INTEGERS 25 (2025), Article A94, Corollary 12 (`integers-2025-A94-cor-12`). -/
public theorem_wanted nColor_oddPartitionParts_byParity_eq_sum_sigmaOdd (m : ℕ) (hm : 1 ≤ m) :
    (∑ s ∈ (nColorPartitions m).filter (fun s => (∀ p ∈ s, Odd p.1) ∧ Even s.card), s.card) +
        ∑ s ∈ (nColorPartitions m).filter (fun s => (∀ p ∈ s, Odd p.1) ∧ Odd s.card), s.card =
      ∑ k ∈ Finset.Icc 1 m,
        sigmaOdd k * ((nColorPartitions (m - k)).filter fun s => ∀ p ∈ s, Odd p.1).card


/-- **Generating functions for the total number of parts of $n$-color partitions.** For
$m \ge 0$ let $T_o(m)$ (resp. $T_e(m)$) be the total number of parts, counted with
multiplicity, over the $n$-color partitions of $m$ having an odd (resp. even) number of parts.
Then, as formal power series in $q$ with rational coefficients,
$$\sum_{m \ge 1} \frac{m q^m}{1 - q^m} =
\prod_{m \ge 1} (1 - q^m)^m \sum_{m \ge 0} \bigl(T_o(m) + T_e(m)\bigr) q^m$$
and
$$\sum_{m \ge 1} \frac{m q^m}{1 + q^m} =
\prod_{m \ge 1} (1 + q^m)^m \sum_{m \ge 0} \bigl(T_o(m) - T_e(m)\bigr) q^m.$$

Source: Shruti Sharma and Amandeep Kaur, *Enumerating Parts of n-Color Partitions*,
INTEGERS 25 (2025), Article A94, Theorem 3 (`integers-2025-A94-thm-3`). -/
public theorem_wanted nColor_totalParts_generatingFunction :
    (∑' m : ℕ, ((m + 1 : ℕ) : ℚ⟦X⟧) * X ^ (m + 1) * (1 - X ^ (m + 1))⁻¹ =
        (∏' m : ℕ, (1 - X ^ (m + 1)) ^ (m + 1) : ℚ⟦X⟧) *
          PowerSeries.mk fun n =>
            ((∑ s ∈ (nColorPartitions n).filter (fun s => Odd s.card), s.card : ℕ) : ℚ) +
              ((∑ s ∈ (nColorPartitions n).filter (fun s => Even s.card), s.card : ℕ) : ℚ)) ∧
      ∑' m : ℕ, ((m + 1 : ℕ) : ℚ⟦X⟧) * X ^ (m + 1) * (1 + X ^ (m + 1))⁻¹ =
        (∏' m : ℕ, (1 + X ^ (m + 1)) ^ (m + 1) : ℚ⟦X⟧) *
          PowerSeries.mk fun n =>
            ((∑ s ∈ (nColorPartitions n).filter (fun s => Odd s.card), s.card : ℕ) : ℚ) -
              ((∑ s ∈ (nColorPartitions n).filter (fun s => Even s.card), s.card : ℕ) : ℚ)

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
public theorem_wanted nColor_evenParts_generatingFunction :
    ∑' m : ℕ, ((2 * (m + 1) : ℕ) : ℚ⟦X⟧) * X ^ (2 * (m + 1)) * (1 - X ^ (2 * (m + 1)))⁻¹ =
      (∏' m : ℕ, (1 - X ^ (m + 1)) ^ (m + 1) : ℚ⟦X⟧) *
        PowerSeries.mk fun n => ((∑ s ∈ nColorPartitions n, (s.filter fun p => Even p.1).card : ℕ) : ℚ)

/-- **Generating function for the number of odd parts in n-color partitions.** For $i \ge 0$ let
$A_o(i)$ be the total number of odd parts (parts of odd size, counted with multiplicity) over the
$n$-color partitions of $i$. Then in the ring $\mathbb{Q}[[q]]$ of formal power series, with
infinite sums and products taken coefficientwise,
$$
\sum_{m \ge 0} \frac{(2m+1)\,q^{2m+1}}{1 - q^{2m+1}} =
\prod_{m \ge 1} (1 - q^m)^m \sum_{i \ge 0} A_o(i)\, q^i.
$$

Source: Shruti Sharma and Amandeep Kaur, *Enumerating Parts of n-Color Partitions*,
INTEGERS 25 (2025), Article A94, Theorem 5 (`integers-2025-A94-thm-5`). -/
public theorem_wanted nColor_oddParts_generatingFunction :
    ∑' m : ℕ, ((2 * m + 1 : ℕ) : ℚ⟦X⟧) * X ^ (2 * m + 1) * (1 - X ^ (2 * m + 1))⁻¹ =
      (∏' m : ℕ, (1 - X ^ (m + 1)) ^ (m + 1) : ℚ⟦X⟧) *
        PowerSeries.mk fun n => ((∑ s ∈ nColorPartitions n, (s.filter fun p => Odd p.1).card : ℕ) : ℚ)

/-- **Generating function for colored parts of multiplicity at least $t$.** Let $t \ge 1$. For
$m \ge 0$ let $N^t(m)$ be the sum, over all $n$-color partitions of $m$, of the number of
distinct colored parts that occur at least $t$ times. Then, as formal power series in $q$ with
rational coefficients,
$$\sum_{m \ge 1} m q^{mt} = \prod_{m \ge 1} (1 - q^m)^m \sum_{m \ge 0} N^t(m) q^m.$$

Source: Shruti Sharma and Amandeep Kaur, *Enumerating Parts of n-Color Partitions*,
INTEGERS 25 (2025), Article A94, Theorem 6 (`integers-2025-A94-thm-6`). -/
public theorem_wanted nColor_partsMultiplicityGe_generatingFunction (t : ℕ) (ht : 1 ≤ t) :
    ∑' m : ℕ, ((m + 1 : ℕ) : ℚ⟦X⟧) * X ^ ((m + 1) * t) =
      (∏' m : ℕ, (1 - X ^ (m + 1)) ^ (m + 1) : ℚ⟦X⟧) *
        PowerSeries.mk fun n =>
          ((∑ s ∈ nColorPartitions n, (s.toFinset.filter fun p => t ≤ s.count p).card : ℕ) : ℚ)

/-- **Generating function for parts in a residue class over n-color partitions.** Let $r$ and
$k$ be natural numbers with $0 < k < r$, and for $i \ge 0$ let $C(k \bmod r, i)$ be the total
number of parts of size congruent to $k$ modulo $r$, counted with multiplicity, over the
$n$-color partitions of $i$. Then in the ring $\mathbb{Q}[[q]]$ of formal power series, with
infinite sums and products taken coefficientwise,
$$
\sum_{m \ge 0} \frac{(rm+k)\,q^{rm+k}}{1 - q^{rm+k}} =
\prod_{m \ge 1} (1 - q^m)^m \sum_{i \ge 0} C(k \bmod r, i)\, q^i.
$$

Source: Shruti Sharma and Amandeep Kaur, *Enumerating Parts of n-Color Partitions*,
INTEGERS 25 (2025), Article A94, Theorem 7 (`integers-2025-A94-thm-7`). -/
public theorem_wanted nColor_partsModEq_generatingFunction (r k : ℕ) (hk : 0 < k) (hkr : k < r) :
    ∑' m : ℕ, ((r * m + k : ℕ) : ℚ⟦X⟧) * X ^ (r * m + k) * (1 - X ^ (r * m + k))⁻¹ =
      (∏' m : ℕ, (1 - X ^ (m + 1)) ^ (m + 1) : ℚ⟦X⟧) *
        PowerSeries.mk fun n =>
          ((∑ s ∈ nColorPartitions n, (s.filter fun p => p.1 % r = k).card : ℕ) : ℚ)

/-- **Generating functions for the parts of distinct $n$-color partitions.** Call an $n$-color
partition distinct when no colored part occurs more than once, and let $C_o(D, m)$ (resp.
$C_e(D, m)$) be the total number of parts over the distinct $n$-color partitions of $m$ with an
odd (resp. even) number of parts. Then, as formal power series in $q$ over $\mathbb{Q}$, with
infinite sums and products taken coefficientwise, both
$$
\sum_{m \ge 1} \frac{m q^m}{1 + q^m} =
\Big(\prod_{m \ge 1} (1 + q^m)^m\Big)^{-1} \sum_{m \ge 0} \big(C_o(D, m) + C_e(D, m)\big) q^m
$$
and
$$
\sum_{m \ge 1} \frac{m q^m}{1 - q^m} =
\Big(\prod_{m \ge 1} (1 - q^m)^m\Big)^{-1} \sum_{m \ge 0} \big(C_o(D, m) - C_e(D, m)\big) q^m
$$
hold.

Source: Shruti Sharma and Amandeep Kaur, *Enumerating Parts of n-Color Partitions*,
INTEGERS 25 (2025), Article A94, Theorem 8 (`integers-2025-A94-thm-8`). -/
public theorem_wanted nColor_distinctTotalParts_generatingFunction :
    (∑' m : ℕ, ((m + 1 : ℕ) : ℚ⟦X⟧) * X ^ (m + 1) * (1 + X ^ (m + 1))⁻¹ =
        (∏' m : ℕ, (1 + X ^ (m + 1)) ^ (m + 1) : ℚ⟦X⟧)⁻¹ *
          PowerSeries.mk fun n =>
            ((∑ s ∈ (nColorPartitions n).filter (fun s => s.Nodup ∧ Odd s.card), s.card : ℕ) : ℚ) +
              ((∑ s ∈ (nColorPartitions n).filter (fun s => s.Nodup ∧ Even s.card), s.card : ℕ) : ℚ)) ∧
      ∑' m : ℕ, ((m + 1 : ℕ) : ℚ⟦X⟧) * X ^ (m + 1) * (1 - X ^ (m + 1))⁻¹ =
        (∏' m : ℕ, (1 - X ^ (m + 1)) ^ (m + 1) : ℚ⟦X⟧)⁻¹ *
          PowerSeries.mk fun n =>
            ((∑ s ∈ (nColorPartitions n).filter (fun s => s.Nodup ∧ Odd s.card), s.card : ℕ) : ℚ) -
              ((∑ s ∈ (nColorPartitions n).filter (fun s => s.Nodup ∧ Even s.card), s.card : ℕ) : ℚ)

/-- **Odd-divisor sum via distinct $n$-color partitions and signed partition counts.** For
$r \ge 0$ let $C_o(D, r)$ (resp. $C_e(D, r)$) be the total number of parts over the $n$-color
partitions of $r$ into an odd (resp. even) number of distinct colored parts, and let
$C_{e-o}(r) = \sum_\lambda (-1)^{\ell(\lambda)}$, the sum running over all $n$-color partitions
$\lambda$ of $r$, where $\ell(\lambda)$ is the number of parts of $\lambda$ counted with
multiplicity. Then for every $m \ge 1$,
$$\sigma_{\mathrm{odd}}(m) =
\sum_{k=1}^{m} \bigl(C_o(D, k) + C_e(D, k)\bigr)\, C_{e-o}(m-k),$$
where $\sigma_{\mathrm{odd}}(m)$ is the sum of the odd divisors of $m$.

This is the reading given by the paper's derivation from Theorem 8 and Eq. (3). As printed,
with the number $C(D, k)$ of $n$-color partitions of $k$ into distinct colored parts in place
of $C_o(D, k) + C_e(D, k)$, it fails at $m = 3$: $\sigma_{\mathrm{odd}}(3) = 4$, but
$\sum_{k=1}^{3} C(D, k)\, C_{e-o}(3-k) = 1 \cdot (-1) + 2 \cdot (-1) + 5 \cdot 1 = 2$.

Source: Shruti Sharma and Amandeep Kaur, *Enumerating Parts of n-Color Partitions*,
INTEGERS 25 (2025), Article A94, Corollary 9 (`integers-2025-A94-cor-9`). -/
public theorem_wanted sigmaOdd_eq_sum_nColor_distinctTotalParts_mul_signed (m : ℕ) (hm : 1 ≤ m) :
    (sigmaOdd m : ℤ) =
      ∑ k ∈ Finset.Icc 1 m,
        (((∑ s ∈ (nColorPartitions k).filter (fun s => s.Nodup ∧ Odd s.card), s.card) +
            ∑ s ∈ (nColorPartitions k).filter (fun s => s.Nodup ∧ Even s.card), s.card : ℕ) : ℤ) *
          ∑ s ∈ nColorPartitions (m - k), (-1 : ℤ) ^ s.card

/-- **Generating function for the number of parts in n-color partitions into odd parts.** For
$i \ge 0$ let $Q(O, i)$ be the total number of parts, counted with multiplicity, over the
$n$-color partitions of $i$ into odd parts (every part has odd size). Then in the ring
$\mathbb{Q}[[q]]$ of formal power series, with infinite sums and products taken coefficientwise,
$$
\sum_{m \ge 0} \frac{(2m+1)\,q^{2m+1}}{1 - q^{2m+1}} =
\prod_{m \ge 0} (1 - q^{2m+1})^{2m+1} \sum_{i \ge 0} Q(O, i)\, q^i.
$$

Source: Shruti Sharma and Amandeep Kaur, *Enumerating Parts of n-Color Partitions*,
INTEGERS 25 (2025), Article A94, Theorem 9 (`integers-2025-A94-thm-9`). -/
public theorem_wanted nColor_oddPartitionParts_generatingFunction :
    ∑' m : ℕ, ((2 * m + 1 : ℕ) : ℚ⟦X⟧) * X ^ (2 * m + 1) * (1 - X ^ (2 * m + 1))⁻¹ =
      (∏' m : ℕ, (1 - X ^ (2 * m + 1)) ^ (2 * m + 1) : ℚ⟦X⟧) *
        PowerSeries.mk fun n =>
          ((∑ s ∈ (nColorPartitions n).filter (fun s => ∀ p ∈ s, Odd p.1), s.card : ℕ) : ℚ)

/-- **Generating function for parts of a given size in distinct $n$-color partitions.** Call an
$n$-color partition distinct when no colored part occurs more than once. For a natural number
$j$, let $Q(D, j, m)$ be the total number of parts of size $j$ (of any color) over the distinct
$n$-color partitions of $m$, and let $C(D, m)$ be the number of distinct $n$-color partitions of
$m$. Then, as formal power series in $q$ over $\mathbb{Q}$,
$$\sum_{m \ge 0} Q(D, j, m) \, q^m = \frac{j q^j}{1 + q^j} \sum_{m \ge 0} C(D, m) \, q^m.$$

The paper assumes $j \ge 1$; for $j = 0$ both sides vanish.

Source: Shruti Sharma and Amandeep Kaur, *Enumerating Parts of n-Color Partitions*,
INTEGERS 25 (2025), Article A94, Theorem 11 (`integers-2025-A94-thm-11`). -/
public theorem_wanted nColor_distinctPartsCountOf_generatingFunction (j : ℕ) :
    (PowerSeries.mk fun n =>
        ((∑ s ∈ (nColorPartitions n).filter (fun s => s.Nodup), (s.filter fun p => p.1 = j).card :
          ℕ) : ℚ)) =
      (j : ℚ⟦X⟧) * X ^ j * (1 + X ^ j)⁻¹ *
        PowerSeries.mk fun n => (((nColorPartitions n).filter fun s => s.Nodup).card : ℚ)

/-- **Parts of n-color partitions into odd parts, by parity of the number of parts.** For
$i \ge 0$ let $U_o(i)$ (resp. $U_e(i)$) be the total number of parts, counted with multiplicity,
over the $n$-color partitions of $i$ into odd parts (every part has odd size) that have an odd
(resp. even) number of parts. Then in the ring $\mathbb{Q}[[q]]$ of formal power series, with
infinite sums and products taken coefficientwise,
$$
\sum_{m \ge 0} \frac{(2m+1)\,q^{2m+1}}{1 - q^{2m+1}} =
\prod_{m \ge 0} (1 - q^{2m+1})^{2m+1} \sum_{i \ge 0} \bigl(U_o(i) + U_e(i)\bigr) q^i
$$
and
$$
\sum_{m \ge 0} \frac{(2m+1)\,q^{2m+1}}{1 + q^{2m+1}} =
\prod_{m \ge 0} (1 + q^{2m+1})^{2m+1} \sum_{i \ge 0} \bigl(U_o(i) - U_e(i)\bigr) q^i.
$$

The paper's printed definition swaps the subscripts ($U_e$ for an odd number of parts); with it
the second identity fails at $q^1$: the left side has coefficient $1$, the right side
$U_o(1) - U_e(1) = 0 - 1 = -1$.

Source: Shruti Sharma and Amandeep Kaur, *Enumerating Parts of n-Color Partitions*,
INTEGERS 25 (2025), Article A94, Theorem 12 (`integers-2025-A94-thm-12`). -/
public theorem_wanted nColor_oddPartitionParts_byParity_generatingFunction :
    (∑' m : ℕ, ((2 * m + 1 : ℕ) : ℚ⟦X⟧) * X ^ (2 * m + 1) * (1 - X ^ (2 * m + 1))⁻¹ =
        (∏' m : ℕ, (1 - X ^ (2 * m + 1)) ^ (2 * m + 1) : ℚ⟦X⟧) *
          PowerSeries.mk fun n =>
            ((∑ s ∈ (nColorPartitions n).filter (fun s => (∀ p ∈ s, Odd p.1) ∧ Odd s.card), s.card :
              ℕ) : ℚ) +
            ((∑ s ∈ (nColorPartitions n).filter (fun s => (∀ p ∈ s, Odd p.1) ∧ Even s.card), s.card :
              ℕ) : ℚ)) ∧
      ∑' m : ℕ, ((2 * m + 1 : ℕ) : ℚ⟦X⟧) * X ^ (2 * m + 1) * (1 + X ^ (2 * m + 1))⁻¹ =
        (∏' m : ℕ, (1 + X ^ (2 * m + 1)) ^ (2 * m + 1) : ℚ⟦X⟧) *
          PowerSeries.mk fun n =>
            ((∑ s ∈ (nColorPartitions n).filter (fun s => (∀ p ∈ s, Odd p.1) ∧ Odd s.card), s.card :
              ℕ) : ℚ) -
            ((∑ s ∈ (nColorPartitions n).filter (fun s => (∀ p ∈ s, Odd p.1) ∧ Even s.card), s.card :
              ℕ) : ℚ)

/-- **Signed odd-divisor sum via $n$-color partitions into odd parts.** For $r \ge 0$ let
$U_o(r)$ (resp. $U_e(r)$) be the total number of parts, counted with multiplicity, over the
$n$-color partitions of $r$ in which every part has odd size and the number of parts is odd
(resp. even), and let $C(O, D, r)$ be the number of $n$-color partitions of $r$ into distinct
colored parts all of odd size. Then for every $m \ge 1$,
$$(-1)^{m+1} \sigma_{\mathrm{odd}}(m) =
\sum_{k=1}^{m} \bigl(U_o(k) - U_e(k)\bigr)\, C(O, D, m-k),$$
where $\sigma_{\mathrm{odd}}(m)$ is the sum of the odd divisors of $m$.

The subscripts of $U_o$ and $U_e$ give the parity of the number of parts. With the printed
(swapped) definition of $U_o$ and $U_e$ the identity fails at $m = 1$: the left side is $1$
and the right side is $(0 - 1) \cdot 1 = -1$.

Source: Shruti Sharma and Amandeep Kaur, *Enumerating Parts of n-Color Partitions*,
INTEGERS 25 (2025), Article A94, Corollary 13 (`integers-2025-A94-cor-13`). -/
public theorem_wanted neg_one_pow_mul_sigmaOdd_eq_sum_nColor_oddPartsDiff (m : ℕ) (hm : 1 ≤ m) :
    (-1 : ℤ) ^ (m + 1) * sigmaOdd m =
      ∑ k ∈ Finset.Icc 1 m,
        (((∑ s ∈ (nColorPartitions k).filter (fun s => (∀ p ∈ s, Odd p.1) ∧ Odd s.card), s.card :
              ℕ) : ℤ) -
            ((∑ s ∈ (nColorPartitions k).filter (fun s => (∀ p ∈ s, Odd p.1) ∧ Even s.card),
              s.card : ℕ) : ℤ)) *
          ((nColorPartitions (m - k)).filter fun s => s.Nodup ∧ ∀ p ∈ s, Odd p.1).card

end

end MetaMathlibExt
