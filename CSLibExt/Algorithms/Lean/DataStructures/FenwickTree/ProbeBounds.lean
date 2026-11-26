/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.FenwickTree

/-!
# Fenwick tree index walks and probe bounds

The zero-based stored index `r` of the [cp-algorithms Fenwick tree article]
(https://cp-algorithms.com/data_structures/fenwick.html) becomes the one-based endpoint
`j = r + 1`. The trailing ones of `r` become trailing zeros of `j`. Thus its block
`[g(r), r]` in zero-based array coordinates is `[j - lowbit j, j)`, and its jumps
`g(r) - 1` and `h(r)` become `j - lowbit j` and `j + lowbit j` after shifting.
The zero-based stopping index `-1` of a prefix walk becomes the unvisited sentinel `0`.

The two walks count visits to stored entries only. They do not model arithmetic time,
the cost of computing `lowbit`, or the cost of copying a shared persistent array.
-/

namespace Cslib.Algorithms.Lean.FenwickTree

private def prefixWalk (j : Nat) : List Nat :=
  if 0 < j then j :: prefixWalk (j - lowbit j) else []
termination_by j
decreasing_by exact Nat.sub_lt ‹0 < j› (lowbit_pos ‹0 < j›)

private theorem prefixWalk_cons {j : Nat} (hj : 0 < j) :
    prefixWalk j = j :: prefixWalk (j - lowbit j) := by
  rw [prefixWalk, ite_eq_left hj]

private theorem prefixWalk_zero : prefixWalk 0 = [] := by
  rw [prefixWalk, ite_eq_right (Nat.lt_irrefl 0)]

/-- **Fenwick prefix visits.** For a natural array length $n$ and requested prefix length $k$,
the list of one-indexed stored entries read by the walk starts at $\min(k,n)$ and repeatedly
subtracts the current index's lowest set bit, stopping before index $0$. The returned list is
in visit order. It is empty if $k=0$ or $n=0$, and a request past the end reads the full prefix.
-/
public def prefixVisits (n k : Nat) : List Nat :=
  prefixWalk (min k n)

/-- **Fenwick point-update visits.** For a natural array length $n$ and one-indexed input
position $i$, list the one-indexed stored entries visited in order, starting from $i$ and
repeatedly adding the current index's lowest set bit. Only indices in $[1,n]$ are visited:
if $i=0$ or $i>n$ (including all inputs when $n=0$), the list is empty. An update at a
zero-indexed array position $p$ uses $i=p+1$. -/
@[expose] public def updateVisits (n i : Nat) : List Nat :=
  if 0 < i ∧ i ≤ n then i :: updateVisits n (i + lowbit i) else []
termination_by n + 1 - i
decreasing_by
  have := lowbit_pos (show 0 < i from ‹0 < i ∧ i ≤ n›.1)
  omega

private theorem updateVisits_cons {n i : Nat} (hi : 0 < i ∧ i ≤ n) :
    updateVisits n i = i :: updateVisits n (i + lowbit i) := by
  rw [updateVisits, ite_eq_left hi]

private theorem updateVisits_nil {n i : Nat} (hi : ¬(0 < i ∧ i ≤ n)) :
    updateVisits n i = [] := by
  rw [updateVisits, ite_eq_right hi]

private theorem two_pow_le_lowbit {j e : Nat} (hj : 0 < j) (he : 2 ^ e ∣ j) :
    2 ^ e ≤ lowbit j := by
  obtain ⟨k, hk⟩ := lowbit_two_pow hj
  by_cases h : e ≤ k
  · rw [hk]
    exact Nat.pow_le_pow_right (by decide) h
  have hd : lowbit j * 2 ∣ j := by
    rw [hk, ← pow_succ]
    exact Nat.dvd_trans (Nat.pow_dvd_pow 2 (by omega : k + 1 ≤ e)) he
  have hmod := Nat.mod_eq_zero_of_dvd (Nat.dvd_div_of_mul_dvd hd)
  have hodd := lowbit_div_odd hj
  omega

private theorem two_mul_lowbit_le_of_dvd {j x : Nat} (hj : 0 < j) (hx : 0 < x)
    (h : 2 * lowbit j ∣ x) : 2 * lowbit j ≤ lowbit x := by
  obtain ⟨e, he⟩ := lowbit_two_pow hj
  rw [he, ← pow_succ'] at h ⊢
  exact two_pow_le_lowbit hx h

private theorem two_mul_lowbit_dvd_steps {j : Nat} (hj : 0 < j) :
    (2 * lowbit j ∣ j - lowbit j) ∧ (2 * lowbit j ∣ j + lowbit j) := by
  let q := (j / lowbit j) / 2
  have hodd := lowbit_div_odd hj
  have he : j / lowbit j = 2 * q + 1 := by omega
  have hfactor : j = (2 * lowbit j) * q + lowbit j := by
    calc
      j = lowbit j * (j / lowbit j) := (Nat.mul_div_cancel' (lowbit_dvd hj)).symm
      _ = _ := by rw [he, Nat.mul_add, Nat.mul_one, ← Nat.mul_assoc, Nat.mul_comm (lowbit j) 2]
  exact ⟨⟨q, by omega⟩, ⟨q + 1, by rw [Nat.mul_succ]; omega⟩⟩

private theorem lowbit_sub_doubles {j : Nat} (hj : 0 < j) (hnext : 0 < j - lowbit j) :
    2 * lowbit j ≤ lowbit (j - lowbit j) :=
  two_mul_lowbit_le_of_dvd hj hnext (two_mul_lowbit_dvd_steps hj).1

private theorem lowbit_add_doubles {j : Nat} (hj : 0 < j) :
    2 * lowbit j ≤ lowbit (j + lowbit j) :=
  two_mul_lowbit_le_of_dvd hj (by omega) (two_mul_lowbit_dvd_steps hj).2

private theorem prefixWalk_blocks (j : Nat) :
    (prefixWalk j).reverse.flatMap (fun x => List.range' (x - lowbit x) (lowbit x)) =
      List.range' 0 j := by
  by_cases hj : 0 < j
  · rw [prefixWalk_cons hj, List.reverse_cons, List.flatMap_append,
      prefixWalk_blocks (j - lowbit j)]
    simpa [Nat.sub_add_cancel (lowbit_le j)] using
      (List.range'_append (s := 0) (m := j - lowbit j) (n := lowbit j) (step := 1))
  · rw [show j = 0 by omega, prefixWalk_zero]
    rfl
termination_by j
decreasing_by exact Nat.sub_lt hj (lowbit_pos hj)

/-- **Fenwick prefix blocks partition the prefix.** For natural array length $n$ and query length
$k$, reverse the visit list (so the blocks are read from left to right) and concatenate the
zero-indexed array intervals $[j-\operatorname{lowbit}(j),j)$ of the visited stored endpoints
$j$. The result is exactly the consecutive list of positions from $0$ up to but excluding
$\min(k,n)$, in increasing order, without omissions or repetitions. It is empty when
$k=0$ or $n=0$, and uses the entire array when $k \ge n$. -/
public theorem prefixVisits_blocks (n k : Nat) :
    (prefixVisits n k).reverse.flatMap (fun j => List.range' (j - lowbit j) (lowbit j)) =
      List.range (min k n) := by
  rw [List.range_eq_range']
  exact prefixWalk_blocks _

private theorem sum_take_eq_range {α : Type*} [AddCommMonoid α] (a : List α) (k : Nat) :
    (a.take k).sum = ((List.range k).map (fun i => a.getD i 0)).sum := by
  induction a generalizing k with
  | nil => simp
  | cons x a ih =>
    cases k with
    | zero => rfl
    | succ k =>
      simp only [List.take_succ_cons, List.sum_cons, ih, List.range_succ_eq_map,
        List.map_cons, List.map_map, List.getD_cons_zero]
      rfl

/-- **Sum of the visited Fenwick prefix blocks.** For a list $a$ over any additive commutative
monoid and any requested length $k$, sum the stored block sums of $a$ at the one-indexed
endpoints visited by the prefix walk of array length $|a|$. This equals the sum of the first
$\min(k,|a|)$ entries of $a$, including $0$ for an empty prefix and the whole sum for
requests beyond the end. -/
public theorem sum_prefixVisits_blockSum {α : Type*} [AddCommMonoid α] (a : List α) (k : Nat) :
    ((prefixVisits a.length k).map (blockSum a)).sum = (a.take k).sum := by
  have h := congrArg (fun js : List Nat => (js.map (fun i => a.getD i 0)).sum)
    (prefixVisits_blocks a.length k)
  rw [List.map_flatMap, List.flatMap, List.sum_flatten, List.map_map] at h
  change (((prefixVisits a.length k).reverse).map (blockSum a)).sum = _ at h
  rw [List.map_reverse, List.sum_reverse] at h
  rw [h, ← sum_take_eq_range, ← List.take_take, List.take_of_length_le (Nat.le_refl _)]

private theorem prefixWalk_bounds_of_mem {k j : Nat} (h : j ∈ prefixWalk k) :
    0 < j ∧ j ≤ k := by
  by_cases hk : 0 < k
  · rw [prefixWalk_cons hk, List.mem_cons] at h
    rcases h with rfl | h
    · exact ⟨hk, Nat.le_refl _⟩
    · have h' := prefixWalk_bounds_of_mem h
      exact ⟨h'.1, Nat.le_trans h'.2 (Nat.sub_le _ _)⟩
  · rw [show k = 0 by omega, prefixWalk_zero] at h
    exact False.elim (List.not_mem_nil h)
termination_by k
decreasing_by exact Nat.sub_lt hk (lowbit_pos hk)

/-- **The Fenwick prefix query sums the visited entries.** Let $t$ represent a list $a$ over
an additive commutative monoid. For every natural requested length $k$, the installed prefix
query of $t$ is the sum of the stored entries at the endpoints in the prefix visit list for
length $t.\mathrm{size}=|a|$. The visit list uses only stored positions from $1$ to
$\min(k,|a|)$, so the dummy entry and out-of-bounds defaults do not contribute. -/
public theorem prefixSum_eq_sum_prefixVisits {α : Type*} [AddCommMonoid α]
    (t : FenwickTree α) {a : List α} (hv : Valid t a) (k : Nat) :
    t.prefixSum k = ((prefixVisits t.size k).map (fun j => t.bit.getD j 0)).sum := by
  rw [prefixSum_eq_take_sum t hv, size_eq_length_of_valid hv,
    ← sum_prefixVisits_blockSum a k]
  congr 1
  apply List.map_congr_left
  intro j hj
  have hb := prefixWalk_bounds_of_mem (show j ∈ prefixWalk (min k a.length) from hj)
  exact (hv.2 j hb.1 (Nat.le_trans hb.2 (Nat.min_le_right _ _))).symm

private theorem lowbit_dvd_lowbit_of_le {i j : Nat} (hi : 0 < i) (hj : 0 < j)
    (h : lowbit i ≤ lowbit j) : lowbit i ∣ lowbit j := by
  obtain ⟨k, hk⟩ := lowbit_two_pow hi
  obtain ⟨m, hm⟩ := lowbit_two_pow hj
  rw [hk, hm] at h ⊢
  exact Nat.pow_dvd_pow 2 ((Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp h)

private theorem add_le_of_dvd_of_lt {a b p : Nat} (ha : p ∣ a) (hb : p ∣ b) (h : a < b) :
    a + p ≤ b := by
  have := Nat.le_of_dvd (by omega : 0 < b - a) (Nat.dvd_sub hb ha)
  omega

-- A jump cannot skip a later endpoint whose block contains the current position.
private theorem update_step_le_of_contains {i j : Nat} (hi : 0 < i) (hij : i < j)
    (hcover : j - lowbit j < i) : i + lowbit i ≤ j := by
  have hj : 0 < j := by omega
  by_cases h : lowbit i ≤ lowbit j
  · exact add_le_of_dvd_of_lt (lowbit_dvd hi)
      (Nat.dvd_trans (lowbit_dvd_lowbit_of_le hi hj h) (lowbit_dvd hj)) hij
  · have h' := add_le_of_dvd_of_lt
      (Nat.dvd_trans (lowbit_dvd_lowbit_of_le hj hi (by omega)) (lowbit_dvd hi)) (lowbit_dvd hj) hij
    omega

private theorem updateVisits_bounds_of_mem {n i j : Nat} (h : j ∈ updateVisits n i) :
    0 < i ∧ i ≤ j ∧ j ≤ n ∧ j - lowbit j ≤ i - lowbit i := by
  by_cases hi : 0 < i ∧ i ≤ n
  · rw [updateVisits_cons hi, List.mem_cons] at h
    rcases h with rfl | h
    · exact ⟨hi.1, Nat.le_refl _, hi.2, Nat.le_refl _⟩
    · obtain ⟨-, hge, hle, hleft⟩ := updateVisits_bounds_of_mem h
      have := lowbit_add_doubles hi.1
      exact ⟨hi.1, by omega, hle, by omega⟩
  · rw [updateVisits_nil hi] at h
    exact False.elim (List.not_mem_nil h)
termination_by n + 1 - i
decreasing_by
  have := lowbit_pos hi.1
  omega

/-- **Exact membership in the Fenwick update walk.** For natural length $n$, one-indexed
input position $i$, and candidate stored endpoint $j$, the update walk visits $j$ if and only
if $j \le n$ and $j-\operatorname{lowbit}(j)< i\le j$ (the one-indexed block ending at $j$
contains $i$). This condition excludes the dummy endpoint $0$ and is impossible for
$i=0$ or $i>n$, including every input when $n=0$. -/
public theorem mem_updateVisits_iff (n i j : Nat) :
    j ∈ updateVisits n i ↔ j ≤ n ∧ j - lowbit j < i ∧ i ≤ j := by
  constructor
  · intro h
    obtain ⟨hpos, hge, hle, hleft⟩ := updateVisits_bounds_of_mem h
    have := lowbit_pos hpos
    exact ⟨hle, by omega, hge⟩
  · rintro ⟨hjn, hcover, hij⟩
    have hi : 0 < i ∧ i ≤ n := by omega
    rw [updateVisits_cons hi, List.mem_cons]
    by_cases he : j = i
    · exact Or.inl he
    · have hstep := update_step_le_of_contains hi.1 (by omega) hcover
      exact Or.inr ((mem_updateVisits_iff n (i + lowbit i) j).2 ⟨hjn, by omega, hstep⟩)
termination_by n + 1 - i
decreasing_by
  have := lowbit_pos hi.1
  omega

/-- **Fenwick update visits are strictly increasing.** For any natural array length $n$ and
one-indexed start $i$, each index in the update visit list is strictly smaller than every
later one, so no stored entry is visited twice. For $i=0$ or $i>n$ the list is empty. -/
public theorem updateVisits_pairwise (n i : Nat) : (updateVisits n i).Pairwise (· < ·) := by
  by_cases hi : 0 < i ∧ i ≤ n
  · rw [updateVisits_cons hi, List.pairwise_cons]
    have hp := lowbit_pos hi.1
    refine ⟨?_, updateVisits_pairwise n (i + lowbit i)⟩
    intro j hj
    have := ((mem_updateVisits_iff _ _ _).mp hj).2.2
    omega
  · rw [updateVisits_nil hi]
    exact List.Pairwise.nil
termination_by n + 1 - i
decreasing_by
  have := lowbit_pos hi.1
  omega

private theorem next_level {j x e : Nat} (he : 2 ^ e ≤ lowbit j)
    (hx : 2 * lowbit j ≤ lowbit x) : 2 ^ (e + 1) ≤ lowbit x := by
  rw [pow_succ']
  exact Nat.le_trans (Nat.mul_le_mul_left 2 he) hx

private theorem level_le_log2 {n j e : Nat} (hj : 0 < j) (hjn : j ≤ n)
    (he : 2 ^ e ≤ lowbit j) : e ≤ n.log2 :=
  (Nat.le_log2 (by omega)).2 (Nat.le_trans he (Nat.le_trans (lowbit_le j) hjn))

-- Each remaining visit spends one level, starting at level at least `e`.
private theorem prefixWalk_length_add_le (n j e : Nat) (hj : 0 < j) (hjn : j ≤ n)
    (he : 2 ^ e ≤ lowbit j) : (prefixWalk j).length + e ≤ n.log2 + 1 := by
  rw [prefixWalk_cons hj, List.length_cons]
  by_cases hnext : 0 < j - lowbit j
  · have h := prefixWalk_length_add_le n (j - lowbit j) (e + 1) hnext (by omega)
      (next_level he (lowbit_sub_doubles hj hnext))
    omega
  · rw [show j - lowbit j = 0 by omega, prefixWalk_zero, List.length_nil]
    have := level_le_log2 hj hjn he
    omega
termination_by j
decreasing_by exact Nat.sub_lt hj (lowbit_pos hj)

private theorem updateVisits_length_add_le (n i e : Nat) (hi : 0 < i ∧ i ≤ n)
    (he : 2 ^ e ≤ lowbit i) : (updateVisits n i).length + e ≤ n.log2 + 1 := by
  rw [updateVisits_cons hi, List.length_cons]
  by_cases hnext : 0 < i + lowbit i ∧ i + lowbit i ≤ n
  · have h := updateVisits_length_add_le n (i + lowbit i) (e + 1) hnext
      (next_level he (lowbit_add_doubles hi.1))
    omega
  · rw [updateVisits_nil hnext, List.length_nil]
    have := level_le_log2 hi.1 hi.2 he
    omega
termination_by n + 1 - i
decreasing_by
  have := lowbit_pos hi.1
  omega

/-- **Logarithmic prefix probe bound.** For every natural array length $n$ and requested
prefix length $k$, the visit list of the prefix walk has length at most
$\lfloor\log_2 n\rfloor+1$ when $n>0$. For $n=0$ or $k=0$ the list is empty; the same
inequality holds with the convention $\operatorname{log2}(0)=0$. -/
public theorem prefixVisits_length_le (n k : Nat) : (prefixVisits n k).length ≤ n.log2 + 1 := by
  change (prefixWalk (min k n)).length ≤ _
  by_cases hm : 0 < min k n
  · simpa using prefixWalk_length_add_le n (min k n) 0 hm (Nat.min_le_right _ _) (lowbit_pos hm)
  · simp [show min k n = 0 by omega, prefixWalk_zero]

/-- **Logarithmic point-update probe bound.** For every natural array length $n$ and
one-indexed input position $i$, the update visits at most $\lfloor\log_2 n\rfloor+1$ entries
when $n>0$. For $i=0$ or $i>n$ the visit list is empty, hence also when $n=0$;
the inequality holds with $\operatorname{log2}(0)=0$. -/
public theorem updateVisits_length_le (n i : Nat) : (updateVisits n i).length ≤ n.log2 + 1 := by
  by_cases hi : 0 < i ∧ i ≤ n
  · simpa using updateVisits_length_add_le n i 0 hi (lowbit_pos hi.1)
  · simp [updateVisits_nil hi]

/-- **Fenwick prefix queries and updates have logarithmically many probes.** For natural
array length $n$, requested prefix length $k$, and one-indexed update position $i$:

* Concatenating the prefix walk's blocks in reverse visit order gives exactly the
  consecutive zero-indexed positions in $[0,\min(k,n))$. The block of the one-indexed
  stored endpoint $j$ is $[j-\operatorname{lowbit}(j),j)$ in zero-indexed coordinates.
* The update walk is strictly increasing and contains exactly the stored endpoints
  $j\le n$ with $j-\operatorname{lowbit}(j)<i\le j$.
* Both visit lists have length at most $\lfloor\log_2 n\rfloor+1$ for $n>0$. The prefix
  list is empty if $k=0$ or $n=0$ and clamps to the full prefix for $k>n$. The update list
  is empty if $i=0$ or $i>n$. The inequalities also hold with $\operatorname{log2}(0)=0$.

The bounds count visited indices, not running time. For a positive index $j$, the quotient
$j/\operatorname{lowbit}(j)$ is odd. Adding or subtracting one copy of the low bit makes the
new index a multiple of twice that low bit. On a nonzero next visit the exponent therefore
strictly increases, and there are only $\lfloor\log_2 n\rfloor+1$ available exponents. -/
public theorem prefixUpdate_probeBounds (n k i : Nat) :
    (prefixVisits n k).reverse.flatMap (fun j => List.range' (j - lowbit j) (lowbit j)) =
      List.range (min k n) ∧
    (updateVisits n i).Pairwise (· < ·) ∧
    (∀ j, j ∈ updateVisits n i ↔ j ≤ n ∧ j - lowbit j < i ∧ i ≤ j) ∧
    (prefixVisits n k).length ≤ n.log2 + 1 ∧ (updateVisits n i).length ≤ n.log2 + 1 :=
  ⟨prefixVisits_blocks n k, updateVisits_pairwise n i, mem_updateVisits_iff n i,
    prefixVisits_length_le n k, updateVisits_length_le n i⟩

end Cslib.Algorithms.Lean.FenwickTree
