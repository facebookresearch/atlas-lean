/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Bioinformatics.Indexing.SuffixArraySearch
public import Cslib.Algorithms.Lean.TimeM

/-!
# Kasai's algorithm for the LCP array

Kasai's algorithm computes the LCP array of a list from its suffix array. It visits the start
positions `i = 0, 1, …, n - 1` in text order and compares the suffix starting at `i` with the
suffix that follows it in suffix-array order, starting from the common-prefix length found at
the previous position minus one. This is correct because, when the suffix at `i` shares `h > 0`
symbols with its successor, the suffix at `i + 1` shares at least `h - 1` symbols with its own
successor; and the carried length then decreases by at most one per position, except where it is
reset to `0`, and never exceeds the length of the current suffix, so the number of symbol
comparisons is linear.

## Main definitions and statements

* `kasai`: Kasai's algorithm.
* `kasai_suffixArray`: given the suffix array, `kasai` returns the LCP array.
* `kasai_time_le`: given any permutation of the positions of a list of length `n`, `kasai` has
  cost at most `4 * n`.

## Implementation notes

The private helpers `timedLcp`, which finds the longest-common-prefix length of two lists by
comparing them symbol by symbol, and `kasaiScan`, the main loop, carry the cost. The cost counts
one unit for each position visited and one unit for each symbol comparison. Finding the rank of a
position in the suffix array, indexing, arithmetic and building lists are free; on a
random-access machine the ranks are tabulated in one linear pass before the main loop, and each
rank lookup then takes constant time.

## References

* cp-algorithms, *Suffix Array*, section "Longest common prefix of two substrings without
  additional memory", <https://cp-algorithms.com/string/suffix-array.html>.
* E. Demaine, *6.851: Advanced Data Structures*, Lecture 16 (scribe notes, Spring 2012), MIT,
  Section 4.1, which attributes the linear-time construction to T. Kasai, G. Lee, H. Arimura,
  S. Arikawa and K. Park, *Linear-time longest-common-prefix computation in suffix arrays and its
  applications*, CPM 2001, LNCS 2089, 181–192.
-/

public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean

universe u

namespace SuffixArray

open Cslib.Bioinformatics.Indexing.SuffixArraySearch

section Timed

variable {α : Type u} [DecidableEq α]

/-- The longest-common-prefix length of two lists, found by comparing them symbol by symbol from
the start; the cost is the number of symbol comparisons. -/
@[no_expose] private def timedLcp : List α → List α → TimeM ℕ ℕ
  | [], _ => return 0
  | _ :: _, [] => return 0
  | a :: x, b :: y => do
      TimeM.tick 1
      if a = b then
        let m ← timedLcp x y
        return m + 1
      else
        return 0

/-- The main loop of Kasai's algorithm: `m` steps from position `i` with carried length `k`. At a
position with a successor `j` in `sa` it records `k` plus the longest-common-prefix length of the
suffixes at `i + k` and `j + k` and carries that value minus one; at a position without one it
records `0` and carries `0`. The cost is one unit per visited position plus the symbol
comparisons. -/
@[no_expose] private def kasaiScan (s : List α) (sa : List ℕ) : ℕ → ℕ → ℕ → TimeM ℕ (List ℕ)
  | 0, _, _ => return []
  | m + 1, i, k => do
      TimeM.tick 1
      if sa.idxOf i + 1 < sa.length then
        let l ← timedLcp (s.drop (i + k)) (s.drop (sa.getD (sa.idxOf i + 1) 0 + k))
        let rest ← kasaiScan s sa m (i + 1) (k + l - 1)
        return (k + l) :: rest
      else
        let rest ← kasaiScan s sa m (i + 1) 0
        return 0 :: rest

/-- **Kasai's algorithm.** Let $s$ be a list of length $n$ and $sa$ a list of natural numbers,
typically the suffix array of $s$. The algorithm visits $i = 0, 1, \dots, n - 1$ in turn, carrying
a length $k$ that starts at $0$. If $i$ occurs in $sa$, first at index $r$, with $r + 1 < |sa|$,
and $j$ is the entry of $sa$ at index $r + 1$, it records at $i$ the value $H_i = k + \ell$, where
$\ell$ is the longest-common-prefix length of the suffixes of $s$ starting at $i + k$ and at
$j + k$, found by symbol comparisons, and sets $k$ to $H_i - 1$ (truncated at $0$); otherwise it
records $H_i = 0$ and sets $k$ to $0$. It returns the list of length $|sa| - 1$ whose $t$-th entry
is $H_{sa_t}$, read as $0$ when $sa_t \ge n$. Its cost is one unit per visited position plus the
number of symbol comparisons.

Source: cp-algorithms, "Suffix Array", section "Longest common prefix of two substrings without
additional memory". -/
def kasai (s : List α) (sa : List ℕ) : TimeM ℕ (List ℕ) := do
  let heights ← kasaiScan s sa s.length 0 0
  return sa.dropLast.map fun i => heights.getD i 0

private theorem timedLcp_ret : ∀ x y : List α, (timedLcp x y).ret = lcp x y
  | [], _ => rfl
  | _ :: _, [] => rfl
  | a :: x, b :: y => by
      by_cases h : a = b
      · simp [timedLcp, lcp, h, timedLcp_ret x y]
      · simp [timedLcp, lcp, h]

private theorem timedLcp_time_le : ∀ x y : List α, (timedLcp x y).time ≤ lcp x y + 1
  | [], _ => by simp [timedLcp]
  | _ :: _, [] => by simp [timedLcp]
  | a :: x, b :: y => by
      by_cases h : a = b
      · have ih := timedLcp_time_le x y
        simp [timedLcp, lcp, h]
        omega
      · simp [timedLcp, lcp, h]

private theorem getD_eq_getElem' {l : List ℕ} {i : ℕ} (h : i < l.length) :
    l.getD i 0 = l[i] :=
  (List.getElem_eq_getD 0).symm

/-- The number of positions in `[i, i + m)` at which the main loop finds no successor. -/
private def resets (sa : List ℕ) (i m : ℕ) : ℕ :=
  ((List.range' i m).filter fun p => !decide (sa.idxOf p + 1 < sa.length)).length

private theorem kasaiScan_time (s : List α) (sa : List ℕ) :
    ∀ m i k, i + m = s.length → k ≤ s.length - i →
      (kasaiScan s sa m i k).time + k ≤ 3 * m + s.length * resets sa i m
  | 0, i, k, him, hk => by
      simp only [kasaiScan, TimeM.time_pure]
      omega
  | m + 1, i, k, him, hk => by
      by_cases hr : sa.idxOf i + 1 < sa.length
      · have hl := lcp_le_left (s.drop (i + k)) (s.drop (sa.getD (sa.idxOf i + 1) 0 + k))
        have ht := timedLcp_time_le (s.drop (i + k)) (s.drop (sa.getD (sa.idxOf i + 1) 0 + k))
        simp only [List.length_drop] at hl
        have ih := kasaiScan_time s sa m (i + 1)
          (k + lcp (s.drop (i + k)) (s.drop (sa.getD (sa.idxOf i + 1) 0 + k)) - 1)
          (by omega) (by omega)
        simp only [resets, List.range'_succ, List.filter_cons, hr, decide_true, Bool.not_true,
          Bool.false_eq_true, ite_false] at ih ⊢
        simp only [kasaiScan, hr, ite_true, TimeM.time_bind, TimeM.time_tick, timedLcp_ret,
          TimeM.time_pure]
        omega
      · have ih := kasaiScan_time s sa m (i + 1) 0 (by omega) (by omega)
        simp only [resets, List.range'_succ, List.filter_cons, hr, decide_false, Bool.not_false,
          ite_true, List.length_cons] at ih ⊢
        simp only [kasaiScan, hr, ite_false, TimeM.time_bind, TimeM.time_tick, TimeM.time_pure]
        rw [Nat.mul_add_one s.length]
        omega

private theorem resets_le_one {n : ℕ} {sa : List ℕ} (hsa : sa.Perm (List.range n)) :
    resets sa 0 n ≤ 1 := by
  have hlen : sa.length = n := by rw [hsa.length_eq, List.length_range]
  have hnodup : ((List.range' 0 n).filter fun p => !decide (sa.idxOf p + 1 < sa.length)).Nodup :=
    (List.nodup_range' (step := 1) (by omega)).filter _
  have hall : ∀ p ∈ (List.range' 0 n).filter (fun p => !decide (sa.idxOf p + 1 < sa.length)),
      p = sa.getD (n - 1) 0 := by
    intro p hp
    simp only [List.mem_filter, List.mem_range'_1, Bool.not_eq_eq_eq_not, Bool.not_true,
      decide_eq_false_iff_not, not_lt] at hp
    have hmem : p ∈ sa := hsa.mem_iff.mpr (List.mem_range.mpr (by omega))
    have hidx := List.idxOf_lt_length_of_mem hmem
    have heq : sa.idxOf p = n - 1 := by omega
    rw [← heq, getD_eq_getElem' hidx, List.getElem_idxOf hidx]
  have hrep := List.eq_replicate_iff.mpr ⟨rfl, hall⟩
  rw [hrep, List.nodup_replicate] at hnodup
  exact hnodup

/-- **Kasai's algorithm runs in linear time.** Let $\alpha$ be a type with decidable equality,
$s$ a list of length $n$ over $\alpha$, and $sa$ any permutation of $0, 1, \dots, n - 1$ (for a
linearly ordered $\alpha$, the suffix array of $s$ is one). Then Kasai's algorithm on $s$ and $sa$
has cost at most $4n$, where the cost counts one unit for each position visited and one unit for
each symbol comparison.

Source: cp-algorithms, "Suffix Array", section "Longest common prefix of two substrings without
additional memory"; E. Demaine, 6.851 Lecture 16 scribe notes (Spring 2012), Section 4.1. -/
theorem kasai_time_le (s : List α) {sa : List ℕ} (hsa : sa.Perm (List.range s.length)) :
    (kasai s sa).time ≤ 4 * s.length := by
  have h := kasaiScan_time s sa s.length 0 0 (by omega) (by omega)
  have hr := resets_le_one hsa
  have hmul : s.length * resets sa 0 s.length ≤ s.length * 1 := Nat.mul_le_mul_left _ hr
  simp only [kasai, TimeM.time_bind, TimeM.time_pure]
  omega

end Timed

section Correctness

variable {α : Type u} [LinearOrder α]

/-- Skipping `k ≤ lcp x y` common symbols leaves the rest of the common prefix. -/
private theorem lcp_eq_add_lcp_drop :
    ∀ (k : ℕ) (x y : List α), k ≤ lcp x y → lcp x y = k + lcp (x.drop k) (y.drop k)
  | 0, x, y, _ => by simp
  | k + 1, [], y, h => by simp at h
  | k + 1, _ :: _, [], h => by simp at h
  | k + 1, a :: x, b :: y, h => by
      by_cases hab : a = b
      · simp only [lcp, hab, ite_true] at h ⊢
        have := lcp_eq_add_lcp_drop k x y (by omega)
        simp only [List.drop_succ_cons]
        omega
      · simp [lcp, hab] at h

/-- A list lying lexicographically between `x` and `z` shares at least `lcp x z` symbols with
`x`. -/
private theorem lcp_le_lcp_of_le_of_le {x y z : List α} (hxy : x ≤ y) (hyz : y ≤ z) :
    lcp x z ≤ lcp x y := by
  have hz : x.take (lcp x z) <+: z := by
    rw [take_lcp_eq x z]
    exact List.take_prefix _ _
  have hy := prefix_of_le_of_le hxy hyz (List.take_prefix _ _) hz
  have hlen : (x.take (lcp x z)).length = lcp x z := by
    rw [List.length_take]
    exact Nat.min_eq_left (lcp_le_left x z)
  refine le_lcp_iff.mpr ⟨?_, ?_⟩
  · have := hy.length_le
    rw [hlen] at this
    exact Nat.le_min.mpr ⟨lcp_le_left x z, this⟩
  · have := List.prefix_iff_eq_take.mp hy
    rw [hlen] at this
    exact this

/-- Later rows of the suffix array hold strictly larger suffixes. -/
private theorem suffix_lt_suffix_of_lt (s : List α) {r r' : ℕ} (hrr' : r < r')
    (hr' : r' < (suffixArray s).length) :
    s.drop ((suffixArray s)[r]'(by omega)) < s.drop (suffixArray s)[r'] := by
  have hp := List.pairwise_map.mp (pairwise_suffix_suffixArray s)
  have hle := List.pairwise_iff_getElem.mp hp r r' (by omega) hr' hrr'
  refine lt_of_le_of_ne hle fun heq => ?_
  have hlen := congrArg List.length heq
  simp only [List.length_drop] at hlen
  have h1 := mem_suffixArray_iff.mp (List.getElem_mem (l := suffixArray s) (n := r) (by omega))
  have h2 := mem_suffixArray_iff.mp (List.getElem_mem (l := suffixArray s) hr')
  have hidx : (suffixArray s)[r]'(by omega) = (suffixArray s)[r'] := by omega
  have := ((suffixArray_nodup s).getElem_inj_iff).mp hidx
  omega

/-- A smaller suffix comes earlier in the suffix array. -/
private theorem idxOf_lt_idxOf (s : List α) {p q : ℕ} (hp : p < s.length) (hq : q < s.length)
    (hpq : s.drop p < s.drop q) :
    (suffixArray s).idxOf p < (suffixArray s).idxOf q := by
  have hpi := List.idxOf_lt_length_of_mem (mem_suffixArray_iff.mpr hp)
  have hqi := List.idxOf_lt_length_of_mem (mem_suffixArray_iff.mpr hq)
  rcases lt_trichotomy ((suffixArray s).idxOf p) ((suffixArray s).idxOf q) with h | h | h
  · exact h
  · have : p = q := by
      rw [← List.getElem_idxOf hpi, ← List.getElem_idxOf hqi]
      simp only [h]
    subst this
    exact absurd hpq (lt_irrefl _)
  · have := suffix_lt_suffix_of_lt s h hpi
    simp only [List.getElem_idxOf] at this
    exact absurd hpq (lt_asymm this)

/-- The value the main loop records at position `i` when its input is the suffix array: the
longest-common-prefix length of the suffix at `i` with the next suffix in suffix-array order,
or `0` when there is none. -/
private def height (s : List α) (i : ℕ) : ℕ :=
  if (suffixArray s).idxOf i + 1 < (suffixArray s).length then
    lcp (s.drop i) (s.drop ((suffixArray s).getD ((suffixArray s).idxOf i + 1) 0))
  else 0

/-- **Height lemma.** If the suffix at `i` shares `h` symbols with its successor in suffix-array
order, the suffix at `i + 1` shares at least `h - 1` symbols with its own successor. -/
private theorem height_sub_one_le (s : List α) {i : ℕ}
    (hi : (suffixArray s).idxOf i + 1 < (suffixArray s).length)
    (hi' : (suffixArray s).idxOf (i + 1) + 1 < (suffixArray s).length) :
    height s i - 1 ≤ height s (i + 1) := by
  have hin : i < s.length := mem_suffixArray_iff.mp (List.idxOf_lt_length_iff.mp (by omega))
  have hin' : i + 1 < s.length :=
    mem_suffixArray_iff.mp (List.idxOf_lt_length_iff.mp (by omega))
  obtain ⟨j, hj⟩ : ∃ j, (suffixArray s)[(suffixArray s).idxOf i + 1] = j := ⟨_, rfl⟩
  have hjn : j < s.length := by
    rw [← hj]
    exact mem_suffixArray_iff.mp (List.getElem_mem _)
  simp only [height, hi, hi', ite_true, getD_eq_getElem' hi, getD_eq_getElem' hi', hj]
  rcases Nat.eq_zero_or_pos (lcp (s.drop i) (s.drop j)) with h0 | hpos
  · omega
  -- The two suffixes start with the same symbol, and the rest of their common prefix follows.
  have hh := hpos
  rw [List.drop_eq_getElem_cons hin, List.drop_eq_getElem_cons hjn] at hh
  have hsym : s[i] = s[j] := by
    by_contra hne
    simp [lcp, hne] at hh
  have htail : lcp (s.drop (i + 1)) (s.drop (j + 1)) = lcp (s.drop i) (s.drop j) - 1 := by
    rw [List.drop_eq_getElem_cons hin, List.drop_eq_getElem_cons hjn]
    simp only [lcp, hsym, ite_true]
    omega
  have hlt : s.drop i < s.drop j := by
    have := suffix_lt_suffix_of_lt s (Nat.lt_succ_self ((suffixArray s).idxOf i)) hi
    simpa only [List.getElem_idxOf, hj] using this
  have hlt' : s.drop (i + 1) < s.drop (j + 1) := by
    rw [List.drop_eq_getElem_cons hin, List.drop_eq_getElem_cons hjn, hsym] at hlt
    rcases List.cons_lt_cons_iff.mp hlt with h' | h'
    · exact absurd h' (lt_irrefl _)
    · exact h'.2
  have hjn' : j + 1 < s.length := by
    by_contra hge
    have hnil : s.drop (j + 1) = [] := List.drop_eq_nil_of_le (by omega)
    rw [hnil] at hlt'
    exact List.not_lt_nil _ hlt'
  -- The successor of `i + 1` lies between it and `j + 1` in suffix-array order.
  have hrank := idxOf_lt_idxOf s hin' hjn' hlt'
  have hji := List.idxOf_lt_length_of_mem (mem_suffixArray_iff.mpr hjn')
  have hlow : s.drop (i + 1) ≤ s.drop (suffixArray s)[(suffixArray s).idxOf (i + 1) + 1] := by
    have := suffix_lt_suffix_of_lt s (Nat.lt_succ_self ((suffixArray s).idxOf (i + 1))) hi'
    rw [List.getElem_idxOf] at this
    exact le_of_lt this
  have hhigh : s.drop (suffixArray s)[(suffixArray s).idxOf (i + 1) + 1] ≤ s.drop (j + 1) := by
    rcases Nat.lt_or_eq_of_le (Nat.succ_le_of_lt hrank) with h' | h'
    · have := suffix_lt_suffix_of_lt s h' hji
      rw [List.getElem_idxOf] at this
      exact le_of_lt this
    · rw [getElem_congr_idx h', List.getElem_idxOf]
  have := lcp_le_lcp_of_le_of_le hlow hhigh
  omega

private theorem kasaiScan_ret (s : List α) :
    ∀ m i k, i + m = s.length →
      ((suffixArray s).idxOf i + 1 < (suffixArray s).length → k ≤ height s i) →
      (kasaiScan s (suffixArray s) m i k).ret = (List.range' i m).map (height s)
  | 0, _, _, _, _ => rfl
  | m + 1, i, k, him, hk => by
      rw [List.range'_succ, List.map_cons]
      by_cases hr : (suffixArray s).idxOf i + 1 < (suffixArray s).length
      · have hki := hk hr
        have hval : k + lcp (s.drop (i + k))
            (s.drop ((suffixArray s).getD ((suffixArray s).idxOf i + 1) 0 + k)) = height s i := by
          simp only [height, hr, ite_true] at hki ⊢
          rw [← List.drop_drop, ← List.drop_drop]
          exact (lcp_eq_add_lcp_drop k _ _ hki).symm
        have ih := kasaiScan_ret s m (i + 1) (height s i - 1) (by omega)
          (fun hr' => height_sub_one_le s hr hr')
        simp only [kasaiScan, hr, ite_true, TimeM.ret_bind, TimeM.ret_pure, timedLcp_ret, hval]
        rw [ih]
      · have ih := kasaiScan_ret s m (i + 1) 0 (by omega) (fun _ => Nat.zero_le _)
        have h0 : height s i = 0 := by simp only [height, hr, ite_false]
        simp only [kasaiScan, hr, ite_false, TimeM.ret_bind, TimeM.ret_pure, ih, h0]

private theorem getElem_adjLcp (s : List α) :
    ∀ (l : List ℕ) (t : ℕ) (ht : t < (adjLcp s l).length),
      (adjLcp s l)[t] = lcp (suffix s (l[t]'(by rw [adjLcp_length] at ht; omega)))
        (suffix s (l[t + 1]'(by rw [adjLcp_length] at ht; omega)))
  | [], t, ht => by simp [adjLcp] at ht
  | [_], t, ht => by simp [adjLcp] at ht
  | i :: j :: rest, 0, _ => by simp [adjLcp]
  | i :: j :: rest, t + 1, ht => by
      simp only [adjLcp, List.getElem_cons_succ]
      exact getElem_adjLcp s (j :: rest) t (by simpa [adjLcp] using ht)

/-- **Kasai's algorithm computes the LCP array.** For a list $s$ over a linearly ordered
alphabet, Kasai's algorithm, given $s$ and the suffix array of $s$, returns the LCP array of $s$:
the list of the longest-common-prefix lengths of the suffixes of $s$ adjacent in suffix-array
order.

Source: cp-algorithms, "Suffix Array", section "Longest common prefix of two substrings without
additional memory". -/
theorem kasai_suffixArray (s : List α) : (kasai s (suffixArray s)).ret = lcpArray s := by
  have hscan := kasaiScan_ret s s.length 0 0 (by omega) (fun _ => Nat.zero_le _)
  rw [← List.range_eq_range'] at hscan
  simp only [kasai, TimeM.ret_bind, TimeM.ret_pure, hscan]
  unfold lcpArray
  apply List.ext_getElem
  · simp [adjLcp_length]
  · intro t h1 h2
    simp only [List.length_map, List.length_dropLast] at h1
    have ht : t < (suffixArray s).length := by omega
    have hmem := mem_suffixArray_iff.mp (List.getElem_mem (l := suffixArray s) ht)
    rw [List.getElem_map, List.getElem_dropLast, getElem_adjLcp]
    rw [getD_eq_getElem' (by simpa using hmem), List.getElem_map, List.getElem_range]
    have hidx := (suffixArray_nodup s).idxOf_getElem t ht
    simp only [height, hidx, show t + 1 < (suffixArray s).length by omega, ite_true,
      getD_eq_getElem' (show t + 1 < (suffixArray s).length by omega), suffix]

end Correctness

end SuffixArray

end Cslib.Algorithms.Lean
