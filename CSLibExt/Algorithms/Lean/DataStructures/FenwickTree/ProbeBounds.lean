/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.FenwickTree
-- Use the private implementation equations to connect probes to the unchanged operations.
import all CSLibExt.Algorithms.Lean.DataStructures.FenwickTree

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

/-- **One step of the Fenwick prefix walk.** For natural array length $n$ and
requested length $k$, let $j=\min(k,n)$. The visit list is empty if $j=0$. Otherwise it
starts with $j$, followed by the prefix visits at length $j-\operatorname{lowbit}(j)$
in the same array. -/
public theorem prefixVisits_eq (n k : Nat) :
    prefixVisits n k = if 0 < min k n then
      min k n :: prefixVisits n (min k n - lowbit (min k n)) else [] := by
  unfold prefixVisits
  by_cases h : 0 < min k n
  · rw [ite_eq_left h, prefixWalk_cons h,
      Nat.min_eq_left (by omega : min k n - lowbit (min k n) ≤ n)]
  · have hz : min k n = 0 := by omega
    rw [ite_eq_right h, hz, prefixWalk_zero]

/-- **Fenwick point-update visits.** For a natural array length $n$ and one-indexed input
position $i$, list the one-indexed stored entries visited in order, starting from $i$ and
repeatedly adding the current index's lowest set bit. Only indices in $[1,n]$ are visited:
if $i=0$ or $i>n$ (including all inputs when $n=0$), the list is empty. An update at a
zero-indexed array position $p$ uses $i=p+1$. -/
public def updateVisits (n i : Nat) : List Nat :=
  if i = 0 then [] else walk n n i

-- Once the fuel covers the remaining distance, its exact value does not affect the list.
private theorem walk_eq_of_enough_fuel (n i f g : Nat) (hi : 0 < i)
    (hf : n + 1 - i ≤ f) (hg : n + 1 - i ≤ g) : walk n f i = walk n g i := by
  by_cases h : i ≤ n
  · have hp := lowbit_pos hi
    cases f with
    | zero => omega
    | succ f =>
      cases g with
      | zero => omega
      | succ g =>
        rw [walk_succ, walk_succ, ite_eq_left h, ite_eq_left h,
          walk_eq_of_enough_fuel n (i + lowbit i) f g (by omega) (by omega) (by omega)]
  · rw [walk_eq_nil_of_lt (by omega : n < i), walk_eq_nil_of_lt (by omega : n < i)]
termination_by n + 1 - i
decreasing_by omega

/-- **A valid Fenwick update step.** For natural array length $n$ and one-indexed start
$1\le i\le n$, the visit list starts with $i$, followed by the update visits starting at
$i+\operatorname{lowbit}(i)$ in the same array. -/
public theorem updateVisits_cons {n i : Nat} (hi : 0 < i ∧ i ≤ n) :
    updateVisits n i = i :: updateVisits n (i + lowbit i) := by
  have hp := lowbit_pos hi.1
  unfold updateVisits
  rw [ite_eq_right (by omega : i ≠ 0), ite_eq_right (by omega : i + lowbit i ≠ 0)]
  cases n with
  | zero => omega
  | succ n =>
    rw [walk_succ (n + 1) n i, ite_eq_left hi.2,
      walk_eq_of_enough_fuel (n + 1) (i + lowbit i) n (n + 1)
        (by omega) (by omega) (by omega)]

/-- **An invalid Fenwick update start has no visits.** For natural array length $n$ and
one-indexed start $i$, if $i$ is not in $[1,n]$ then the update visit list is empty. -/
public theorem updateVisits_nil {n i : Nat} (hi : ¬(0 < i ∧ i ≤ n)) :
    updateVisits n i = [] := by
  unfold updateVisits
  by_cases hz : i = 0
  · rw [ite_eq_left hz]
  · rw [ite_eq_right hz, walk_eq_nil_of_lt (by omega : n < i)]

private theorem lowbit_sub_doubles {j : Nat} (hj : 0 < j) (hnext : 0 < j - lowbit j) :
    2 * lowbit j ≤ lowbit (j - lowbit j) := by
  obtain ⟨e, he⟩ := lowbit_two_pow hj
  have hodd := lowbit_div_odd hj
  let q := j / lowbit j / 2
  have hq : j / lowbit j = 2 * q + 1 := by omega
  have hfactor : j = (2 * lowbit j) * q + lowbit j := by
    calc
      j = lowbit j * (j / lowbit j) := (Nat.mul_div_cancel' (lowbit_dvd hj)).symm
      _ = _ := by rw [hq, Nat.mul_add, Nat.mul_one, ← Nat.mul_assoc, Nat.mul_comm (lowbit j) 2]
  have hdvd : 2 * lowbit j ∣ j - lowbit j := ⟨q, by omega⟩
  have hpow : 2 ^ (e + 1) ∣ j - lowbit j := by
    simpa only [pow_succ', ← he] using hdvd
  calc
    2 * lowbit j = 2 ^ (e + 1) := by rw [he, pow_succ']
    _ ≤ _ := two_pow_le_lowbit hnext hpow

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
  rw [h, ← take_sum_eq, ← List.take_take, List.take_of_length_le (Nat.le_refl _)]

-- The trace is proved against the operational equations, not against `Valid` or `take`.
private theorem prefixAux_eq_trace {α : Type*} [AddCommMonoid α] (bit : Array α)
    (fuel k : Nat) (h : k ≤ fuel) :
    prefixAux bit fuel k = ((prefixWalk k).map (fun j => bit.getD j 0)).sum := by
  induction fuel generalizing k with
  | zero =>
    have hk : k = 0 := by omega
    subst k
    rw [prefixWalk_zero]
    rfl
  | succ fuel ih =>
    rw [prefixAux_succ]
    by_cases hk : k = 0
    · subst k
      rw [ite_eq_left rfl, prefixWalk_zero]
      rfl
    · have hj : 0 < k := by omega
      have hp := lowbit_pos hj
      rw [ite_eq_right hk, prefixWalk_cons hj, List.map_cons, List.sum_cons,
        ih (k - lowbit k) (by omega)]

/-- **The Fenwick prefix query sums the visited entries.** For any Fenwick tree $t$
over an additive commutative monoid and any natural query length $k$, the result is the
sum of the stored entries at the one-indexed endpoints in the prefix visit list for length
$t.\mathrm{size}$ and request $k$. The list records the indices from the query's recursion
in order, with no representation invariant on the stored array. The query clamps to the tree
size and the sum is zero if the clamped length is zero. -/
public theorem prefixSum_eq_sum_prefixVisits {α : Type*} [AddCommMonoid α]
    (t : FenwickTree α) (k : Nat) :
    t.prefixSum k = ((prefixVisits t.size k).map (fun j => t.bit.getD j 0)).sum :=
  prefixAux_eq_trace t.bit _ _ (Nat.le_refl _)

/-- **Exact membership in the Fenwick update walk.** For natural length $n$, one-indexed
input position $i$, and candidate stored endpoint $j$, the update walk visits $j$ if and only
if $j \le n$ and $j-\operatorname{lowbit}(j)< i\le j$ (the one-indexed block ending at $j$
contains $i$). This condition excludes the dummy endpoint $0$ and is impossible for
$i=0$ or $i>n$, including every input when $n=0$. -/
public theorem mem_updateVisits_iff (n i j : Nat) :
    j ∈ updateVisits n i ↔ j ≤ n ∧ j - lowbit j < i ∧ i ≤ j := by
  by_cases hz : i = 0
  · simp [updateVisits, hz]
  have hi : 0 < i := by omega
  rw [updateVisits, ite_eq_right hz]
  constructor
  · intro h
    obtain ⟨hge, hle, hleft⟩ := mem_walk hi h
    have hp := lowbit_pos hi
    exact ⟨hle, by omega, hge⟩
  · rintro ⟨hjn, hcover, hij⟩
    exact mem_walk_of hi hij hjn hcover (by omega)

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

/-- **The Fenwick update writes at the visited endpoints.** For any Fenwick tree $t$ over an
additive commutative monoid, zero-indexed array position $i$, increment $δ$, and natural
stored index $j$, reading index $j$ (with default $0$) after the update gives its old value
plus $δ$ if $j$ belongs to the update visit list for size $t.\mathrm{size}$ and start $i+1$,
and its old value otherwise. This holds for every stored array, including an empty array,
without a representation invariant. The list is the one over which the implementation folds;
each visited index is in bounds and the dummy entry is never visited. If $i\ge t.\mathrm{size}$
the list is empty. -/
public theorem getD_add_eq {α : Type*} [AddCommMonoid α] (t : FenwickTree α)
    (i : Nat) (δ : α) (j : Nat) :
    (t.add i δ).bit.getD j 0 =
      t.bit.getD j 0 + (if j ∈ updateVisits t.size (i + 1) then δ else 0) := by
  unfold updateVisits
  simp only [Nat.add_one_ne_zero, ite_false]
  unfold add
  apply getD_foldl_addAt _ _ (walk_nodup (by omega))
  intro x hx
  have hb := mem_walk (by omega : 0 < i + 1) hx
  unfold size at hb
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
      (next_level he (two_mul_lowbit_le_lowbit_add hi.1))
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

The prefix trace projects the reads from `prefixSum`'s recursion. The `add` operation at
zero-indexed position $p$ folds over precisely `updateVisits n (p+1)`, reading and writing
once per visit. The bounds count visited indices, not running time.
For a positive index $j$, the quotient $j/\operatorname{lowbit}(j)$ is odd. Adding or subtracting
one copy of the low bit makes the
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
