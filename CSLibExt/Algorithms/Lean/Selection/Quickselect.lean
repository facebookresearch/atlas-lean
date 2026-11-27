/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Sort.Partition
public import Mathlib.Data.List.Sort
import Mathlib.Data.Nat.Choose.Basic

/-!
# Deterministic quickselect

This module adapts selection by partitioning from Cormen, Leiserson, Rivest, and Stein,
*Introduction to Algorithms*, 4th ed., Section 9.2, to immutable lists. Ranks are zero-based,
the first element is the deterministic pivot, and a three-way partition handles duplicate ranks.

Each element comparison costs one tick; rank checks, dispatch, list construction, and recursion
are free. The proved bound is worst-case; there is no randomized or expected-linear claim.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.TimeM

universe u

variable {α : Type u} [LinearOrder α]

/-- **Quickselect.** Deterministic quickselect takes a list $L$ over a linear order and a
zero-based rank $k$ and returns an element or no element, together with its cost, the number
of element comparisons it makes. If $k \ge |L|$, it returns no element at no cost. Otherwise
it runs the following recursion, starting from the list $L$ and the rank $k$. On an empty list
it returns no element. On a list with first entry $p$ and remaining entries $T$, and a rank
$r$, it forms the three-way partition of $T$ around $p$, with blocks $B$, $E$, $A$ of entries
below, equal to and above $p$, at a cost of $|T|$ comparisons. If $r < |B|$, it recurses on
$B$ with rank $r$; if $|B| \le r < |B| + |E| + 1$, it returns $p$; otherwise it recurses on
$A$ with rank $r - (|B| + |E| + 1)$.

The recursion carries a fuel counter that starts at $|L|$ and drops by one per call, and it
returns no element when the fuel is exhausted; since every recursive call is on a strictly
shorter list, the fuel never runs out on a nonempty list. -/
def quickselect (xs : List α) (k : Nat) : TimeM Nat (Option α) :=
  let rec loop : Nat → List α → Nat → TimeM Nat (Option α)
    | 0, _, _ => pure none
    | _ + 1, [], _ => pure none
    | fuel + 1, pivot :: tail, rank => do
        let parts ← partition3 pivot tail
        if rank < parts.below.length then
          loop fuel parts.below rank
        else if rank < parts.below.length + parts.equal.length + 1 then
          return some pivot
        else
          loop fuel parts.above
            (rank - (parts.below.length + parts.equal.length + 1))
  if k < xs.length then loop xs.length xs k else pure none

private theorem quickselect_loop_eq_none_iff (fuel : Nat) (xs : List α) (k : Nat)
    (hlen : xs.length ≤ fuel) :
    (quickselect.loop fuel xs k).ret = none ↔ xs.length ≤ k := by
  induction fuel generalizing xs k with
  | zero =>
      cases xs with
      | nil => simp [quickselect.loop]
      | cons x xs => simp at hlen
  | succ fuel ih =>
      cases xs with
      | nil => simp [quickselect.loop]
      | cons pivot tail =>
          have htail : tail.length ≤ fuel := by
            simpa only [List.length_cons, Nat.succ_le_succ_iff] using hlen
          generalize hparts : (partition3 pivot tail).ret = parts
          have hpartsLength := partition3_length pivot tail
          rw [hparts] at hpartsLength
          have hbelowFuel : parts.below.length ≤ fuel := by omega
          have haboveFuel : parts.above.length ≤ fuel := by omega
          by_cases hbelowRank : k < parts.below.length
          · simp [quickselect.loop, hparts, hbelowRank,
              ih parts.below k hbelowFuel]
            omega
          · by_cases hblockRank :
                k < parts.below.length + parts.equal.length + 1
            · simp [quickselect.loop, hparts, hbelowRank, hblockRank]
              omega
            · have habove := ih parts.above
                (k - (parts.below.length + parts.equal.length + 1)) haboveFuel
              simp [quickselect.loop, hparts, hbelowRank, hblockRank, habove]
              omega

/-- **Quickselect fails exactly out of range.** Let $L$ be a list over a linear order and let
$k$ be a natural number. Quickselect on $L$ with zero-based rank $k$ returns no element if and
only if $|L| \le k$. -/
theorem quickselect_eq_none_iff (xs : List α) (k : Nat) :
    (quickselect xs k).ret = none ↔ xs.length ≤ k := by
  by_cases hk : k < xs.length
  · simp [quickselect, hk,
      quickselect_loop_eq_none_iff xs.length xs k (Nat.le_refl _)]
  · simp [quickselect, hk]
    omega

private theorem countP_cons_eq_below (pivot : α) (xs : List α) (p : α → Bool)
    (hpivot : p pivot = false)
    (hequal : ∀ x ∈ (partition3 pivot xs).ret.equal, p x = false)
    (habove : ∀ x ∈ (partition3 pivot xs).ret.above, p x = false) :
    (pivot :: xs).countP p = (partition3 pivot xs).ret.below.countP p := by
  have hparts := partition3_correct pivot xs
  have hequalZero : (partition3 pivot xs).ret.equal.countP p = 0 :=
    List.countP_eq_zero.2 fun x hx => by
      simp [hequal x hx]
  have haboveZero : (partition3 pivot xs).ret.above.countP p = 0 :=
    List.countP_eq_zero.2 fun x hx => by
      simp [habove x hx]
  have hcount := hparts.1.countP_eq p
  calc
    (pivot :: xs).countP p = xs.countP p := by
      simp [hpivot]
    _ = ((partition3 pivot xs).ret.below ++
        (partition3 pivot xs).ret.equal ++
        (partition3 pivot xs).ret.above).countP p := hcount.symm
    _ = (partition3 pivot xs).ret.below.countP p := by
      simp [List.countP_append, hequalZero, haboveZero]

private theorem countP_cons_eq_block_add_above (pivot : α) (xs : List α)
    (p : α → Bool)
    (hpivot : p pivot = true)
    (hbelow : ∀ x ∈ (partition3 pivot xs).ret.below, p x = true)
    (hequal : ∀ x ∈ (partition3 pivot xs).ret.equal, p x = true) :
    (pivot :: xs).countP p =
      (partition3 pivot xs).ret.below.length +
        (partition3 pivot xs).ret.equal.length + 1 +
        (partition3 pivot xs).ret.above.countP p := by
  have hparts := partition3_correct pivot xs
  have hbelowCount :
      (partition3 pivot xs).ret.below.countP p =
        (partition3 pivot xs).ret.below.length :=
    List.countP_eq_length.2 fun x hx => by
      simp [hbelow x hx]
  have hequalCount :
      (partition3 pivot xs).ret.equal.countP p =
        (partition3 pivot xs).ret.equal.length :=
    List.countP_eq_length.2 fun x hx => by
      simp [hequal x hx]
  have hcount := hparts.1.countP_eq p
  simp only [List.countP_append, hbelowCount, hequalCount] at hcount
  simp [hpivot]
  omega

/-- **Counting through the below block.** Let $L$ be a list over a linear order, let $p$ be an
element, let $q$ be a Boolean predicate on the elements, and let $B$, $E$, $A$ be the blocks of
entries below, equal to and above $p$ in the three-way partition of $L$ around $p$. If $q$ is
false on every entry of $E$ and on every entry of $A$, then the number of entries of $L$
satisfying $q$ equals the number of entries of $B$ satisfying $q$, both counted with
multiplicity. -/
theorem partition3_countP_eq_below {α : Type u} [LinearOrder α]
    (pivot : α) (xs : List α) (p : α → Bool)
    (hequal : ∀ x ∈ (partition3 pivot xs).ret.equal, p x = false)
    (habove : ∀ x ∈ (partition3 pivot xs).ret.above, p x = false) :
    xs.countP p = (partition3 pivot xs).ret.below.countP p := by
  have hparts := partition3_correct pivot xs
  have hequalZero : (partition3 pivot xs).ret.equal.countP p = 0 :=
    List.countP_eq_zero.2 fun x hx => by
      simp [hequal x hx]
  have haboveZero : (partition3 pivot xs).ret.above.countP p = 0 :=
    List.countP_eq_zero.2 fun x hx => by
      simp [habove x hx]
  have hcount := hparts.1.countP_eq p
  simp only [List.countP_append, hequalZero, haboveZero, Nat.add_zero] at hcount
  exact hcount.symm

/-- **Counting through the above block.** Let $L$ be a list over a linear order, let $p$ be an
element, let $q$ be a Boolean predicate on the elements, and let $B$, $E$, $A$ be the blocks of
entries below, equal to and above $p$ in the three-way partition of $L$ around $p$. If $q$ is
true on every entry of $B$ and on every entry of $E$, then the number of entries of $L$
satisfying $q$ equals $|B| + |E|$ plus the number of entries of $A$ satisfying $q$, all counted
with multiplicity. -/
theorem partition3_countP_eq_block_add_above {α : Type u} [LinearOrder α]
    (pivot : α) (xs : List α) (p : α → Bool)
    (hbelow : ∀ x ∈ (partition3 pivot xs).ret.below, p x = true)
    (hequal : ∀ x ∈ (partition3 pivot xs).ret.equal, p x = true) :
    xs.countP p = (partition3 pivot xs).ret.below.length +
      (partition3 pivot xs).ret.equal.length + (partition3 pivot xs).ret.above.countP p := by
  have hparts := partition3_correct pivot xs
  have hbelowCount :
      (partition3 pivot xs).ret.below.countP p =
        (partition3 pivot xs).ret.below.length :=
    List.countP_eq_length.2 fun x hx => by
      simp [hbelow x hx]
  have hequalCount :
      (partition3 pivot xs).ret.equal.countP p =
        (partition3 pivot xs).ret.equal.length :=
    List.countP_eq_length.2 fun x hx => by
      simp [hequal x hx]
  have hcount := hparts.1.countP_eq p
  simp only [List.countP_append, hbelowCount, hequalCount] at hcount
  exact hcount.symm

private theorem count_lt_pivot (pivot : α) (xs : List α) :
    (pivot :: xs).countP (fun x => decide (x < pivot)) =
      (partition3 pivot xs).ret.below.length := by
  have hparts := partition3_correct pivot xs
  have hcount := countP_cons_eq_below pivot xs (fun x => decide (x < pivot))
    (by simp)
    (fun x hx => by simp [hparts.2.2.1 x hx])
    (fun x hx => by
      have h := hparts.2.2.2 x hx
      simp [not_lt_of_ge h.le])
  have hbelowCount :
      (partition3 pivot xs).ret.below.countP (fun x => decide (x < pivot)) =
        (partition3 pivot xs).ret.below.length :=
    List.countP_eq_length.2 fun x hx => by
      simp [hparts.2.1 x hx]
  exact hcount.trans hbelowCount

private theorem count_le_pivot (pivot : α) (xs : List α) :
    (pivot :: xs).countP (fun x => decide (x ≤ pivot)) =
      (partition3 pivot xs).ret.below.length +
        (partition3 pivot xs).ret.equal.length + 1 := by
  have hparts := partition3_correct pivot xs
  have hcount := countP_cons_eq_block_add_above pivot xs
    (fun x => decide (x ≤ pivot)) (by simp)
    (fun x hx => by simp [(hparts.2.1 x hx).le])
    (fun x hx => by simp [hparts.2.2.1 x hx])
  have haboveZero :
      (partition3 pivot xs).ret.above.countP (fun x => decide (x ≤ pivot)) = 0 :=
    List.countP_eq_zero.2 fun x hx => by
      simp [not_le_of_gt (hparts.2.2.2 x hx)]
  simpa [haboveZero] using hcount

/-- **Entries below the pivot.** Let $L$ be a list over a linear order, let $p$ be an element,
and let $B$ be the block of entries below $p$ in the three-way partition of $L$ around $p$.
Then the number of entries of $L$ that are strictly less than $p$, counted with multiplicity,
equals $|B|$. -/
theorem partition3_count_lt {α : Type u} [LinearOrder α] (pivot : α) (xs : List α) :
    xs.countP (fun x => decide (x < pivot)) = (partition3 pivot xs).ret.below.length := by
  simpa using count_lt_pivot pivot xs

/-- **Entries at most the pivot.** Let $L$ be a list over a linear order, let $p$ be an element,
and let $B$ and $E$ be the blocks of entries below and equal to $p$ in the three-way partition
of $L$ around $p$. Then the number of entries of $L$ that are at most $p$, counted with
multiplicity, equals $|B| + |E|$. -/
theorem partition3_count_le {α : Type u} [LinearOrder α] (pivot : α) (xs : List α) :
    xs.countP (fun x => decide (x ≤ pivot)) =
      (partition3 pivot xs).ret.below.length + (partition3 pivot xs).ret.equal.length := by
  have h := count_le_pivot pivot xs
  have hcons : (pivot :: xs).countP (fun x => decide (x ≤ pivot)) =
      xs.countP (fun x => decide (x ≤ pivot)) + 1 := by simp
  rw [hcons] at h
  omega

private theorem count_lt_eq_below_of_lt (pivot : α) (xs : List α) {x : α}
    (hx : x < pivot) :
    (pivot :: xs).countP (fun y => decide (y < x)) =
      (partition3 pivot xs).ret.below.countP (fun y => decide (y < x)) := by
  have hparts := partition3_correct pivot xs
  exact countP_cons_eq_below pivot xs (fun y => decide (y < x))
    (by simp [not_lt_of_ge hx.le])
    (fun y hy => by
      rw [hparts.2.2.1 y hy]
      simp [not_lt_of_ge hx.le])
    (fun y hy => by
      have hxy := hx.trans (hparts.2.2.2 y hy)
      simp [not_lt_of_ge hxy.le])

private theorem count_le_eq_below_of_lt (pivot : α) (xs : List α) {x : α}
    (hx : x < pivot) :
    (pivot :: xs).countP (fun y => decide (y ≤ x)) =
      (partition3 pivot xs).ret.below.countP (fun y => decide (y ≤ x)) := by
  have hparts := partition3_correct pivot xs
  exact countP_cons_eq_below pivot xs (fun y => decide (y ≤ x))
    (by simp [not_le_of_gt hx])
    (fun y hy => by
      rw [hparts.2.2.1 y hy]
      simp [not_le_of_gt hx])
    (fun y hy => by
      have hxy := hx.trans (hparts.2.2.2 y hy)
      simp [not_le_of_gt hxy])

private theorem count_lt_eq_block_add_above_of_gt (pivot : α) (xs : List α) {x : α}
    (hx : pivot < x) :
    (pivot :: xs).countP (fun y => decide (y < x)) =
      (partition3 pivot xs).ret.below.length +
        (partition3 pivot xs).ret.equal.length + 1 +
        (partition3 pivot xs).ret.above.countP (fun y => decide (y < x)) := by
  have hparts := partition3_correct pivot xs
  exact countP_cons_eq_block_add_above pivot xs (fun y => decide (y < x))
    (by simp [hx])
    (fun y hy => by simp [(hparts.2.1 y hy).trans hx])
    (fun y hy => by simp [hparts.2.2.1 y hy, hx])

private theorem count_le_eq_block_add_above_of_gt (pivot : α) (xs : List α) {x : α}
    (hx : pivot < x) :
    (pivot :: xs).countP (fun y => decide (y ≤ x)) =
      (partition3 pivot xs).ret.below.length +
        (partition3 pivot xs).ret.equal.length + 1 +
        (partition3 pivot xs).ret.above.countP (fun y => decide (y ≤ x)) := by
  have hparts := partition3_correct pivot xs
  exact countP_cons_eq_block_add_above pivot xs (fun y => decide (y ≤ x))
    (by simp [hx.le])
    (fun y hy => by simp [((hparts.2.1 y hy).trans hx).le])
    (fun y hy => by simp [hparts.2.2.1 y hy, hx.le])

private theorem quickselect_loop_correct (fuel : Nat) (xs : List α) (k : Nat) (x : α)
    (hlen : xs.length ≤ fuel)
    (hresult : (quickselect.loop fuel xs k).ret = some x) :
    x ∈ xs ∧
      xs.countP (fun y => decide (y < x)) ≤ k ∧
      k < xs.countP (fun y => decide (y ≤ x)) := by
  induction fuel generalizing xs k x with
  | zero =>
      cases xs with
      | nil => simp [quickselect.loop] at hresult
      | cons y ys => simp at hlen
  | succ fuel ih =>
      cases xs with
      | nil => simp [quickselect.loop] at hresult
      | cons pivot tail =>
          have htail : tail.length ≤ fuel := by
            simpa only [List.length_cons, Nat.succ_le_succ_iff] using hlen
          generalize hparts : (partition3 pivot tail).ret = parts
          have hpartsCorrect := partition3_correct pivot tail
          rw [hparts] at hpartsCorrect
          obtain ⟨hpartsPerm, hbelow, hequal, habove⟩ := hpartsCorrect
          have hpartsLength := partition3_length pivot tail
          rw [hparts] at hpartsLength
          have hbelowFuel : parts.below.length ≤ fuel := by omega
          have haboveFuel : parts.above.length ≤ fuel := by omega
          by_cases hbelowRank : k < parts.below.length
          · have hrecursive :
                (quickselect.loop fuel parts.below k).ret = some x := by
              simpa [quickselect.loop, hparts, hbelowRank] using hresult
            obtain ⟨hxBelow, hlt, hle⟩ :=
              ih parts.below k x hbelowFuel hrecursive
            have hxpivot : x < pivot := hbelow x hxBelow
            have hxTail : x ∈ tail :=
              hpartsPerm.mem_iff.mp (by simp [hxBelow])
            have hcountLT := count_lt_eq_below_of_lt pivot tail hxpivot
            have hcountLE := count_le_eq_below_of_lt pivot tail hxpivot
            rw [hparts] at hcountLT hcountLE
            refine ⟨by simp [hxTail], ?_, ?_⟩
            · omega
            · omega
          · by_cases hblockRank :
                k < parts.below.length + parts.equal.length + 1
            · have hpivotResult : (some pivot : Option α) = some x := by
                simpa [quickselect.loop, hparts, hbelowRank, hblockRank] using hresult
              have hxpivot : x = pivot := (Option.some.inj hpivotResult).symm
              subst x
              have hcountLT := count_lt_pivot pivot tail
              have hcountLE := count_le_pivot pivot tail
              rw [hparts] at hcountLT hcountLE
              refine ⟨by simp, ?_, ?_⟩
              · omega
              · omega
            · let block := parts.below.length + parts.equal.length + 1
              have hrecursive :
                  (quickselect.loop fuel parts.above (k - block)).ret = some x := by
                simpa [quickselect.loop, hparts, hbelowRank, hblockRank, block] using
                  hresult
              obtain ⟨hxAbove, hlt, hle⟩ :=
                ih parts.above (k - block) x haboveFuel hrecursive
              have hpivotx : pivot < x := habove x hxAbove
              have hxTail : x ∈ tail :=
                hpartsPerm.mem_iff.mp (by simp [hxAbove])
              have hcountLT := count_lt_eq_block_add_above_of_gt pivot tail hpivotx
              have hcountLE := count_le_eq_block_add_above_of_gt pivot tail hpivotx
              rw [hparts] at hcountLT hcountLE
              refine ⟨by simp [hxTail], ?_, ?_⟩
              · dsimp [block] at hlt hle ⊢
                omega
              · dsimp [block] at hlt hle ⊢
                omega

/-- **Correctness of quickselect.** Let $L$ be a list over a linear order and let $k$ be a
natural number. If quickselect on $L$ with zero-based rank $k$ returns an element $x$, then $x$
is an entry of $L$, and, counting entries of $L$ with multiplicity, the number of entries less
than $x$ is at most $k$ and $k$ is less than the number of entries at most $x$.

Thus $x$ occupies zero-based position $k$ in the sorted order of $L$, also when $x$ is repeated. -/
theorem quickselect_correct {xs : List α} {k : Nat} {x : α}
    (hresult : (quickselect xs k).ret = some x) :
    x ∈ xs ∧
      xs.countP (fun y => decide (y < x)) ≤ k ∧
      k < xs.countP (fun y => decide (y ≤ x)) := by
  by_cases hk : k < xs.length
  · have hloop : (quickselect.loop xs.length xs k).ret = some x := by
      simpa [quickselect, hk] using hresult
    exact quickselect_loop_correct xs.length xs k x (Nat.le_refl _) hloop
  · simp [quickselect, hk] at hresult

private theorem getElem?_eq_some_of_count_rank {ys : List α} {k : Nat} {x : α}
    (hsorted : ys.Pairwise (· ≤ ·))
    (hlt : ys.countP (fun y => decide (y < x)) ≤ k)
    (hle : k < ys.countP (fun y => decide (y ≤ x))) : ys[k]? = some x := by
  induction ys generalizing k with
  | nil => simp at hle
  | cons a tail ih =>
      obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp hsorted
      have hax : a ≤ x := by
        by_contra h
        have hxa : x < a := lt_of_not_ge h
        have hzero : tail.countP (fun y => decide (y ≤ x)) = 0 :=
          List.countP_eq_zero.2 fun y hy => by
            simp [not_le_of_gt (hxa.trans_le (hhead y hy))]
        simp [hzero, not_le_of_gt hxa] at hle
      cases k with
      | zero =>
          have hxa : x ≤ a := by
            by_contra h
            have hltax : a < x := lt_of_not_ge h
            simp [hltax] at hlt
          simp [le_antisymm hax hxa]
      | succ k =>
          have hleTail : k < tail.countP (fun y => decide (y ≤ x)) := by
            simp [hax] at hle
            omega
          have hltTail : tail.countP (fun y => decide (y < x)) ≤ k := by
            by_cases hltax : a < x
            · simp [hltax] at hlt
              omega
            · have hxa : x ≤ a := le_of_not_gt hltax
              have hzero : tail.countP (fun y => decide (y < x)) = 0 :=
                List.countP_eq_zero.2 fun y hy => by
                  simp [not_lt_of_ge (hxa.trans (hhead y hy))]
              simp [hzero]
          simpa only [List.getElem?_cons_succ] using ih htail hltTail hleTail

/-- **Quickselect agrees with sorting.** Let $L$ be a list over a linear order, let $S$ be the
insertion sort of $L$ in nondecreasing order, and let $k$ be a natural number. If $k < |L|$,
quickselect on $L$ with zero-based rank $k$ returns the entry of $S$ at zero-based position $k$;
if $k \ge |L|$, it returns no element. -/
theorem quickselect_eq_getElem?_insertionSort (xs : List α) (k : Nat) :
    (quickselect xs k).ret = (xs.insertionSort (· ≤ ·))[k]? := by
  cases hresult : (quickselect xs k).ret with
  | none =>
      have hk := (quickselect_eq_none_iff xs k).mp hresult
      symm
      exact List.getElem?_eq_none_iff.mpr (by simpa using hk)
  | some x =>
      obtain ⟨_, hlt, hle⟩ := quickselect_correct hresult
      have hperm := List.perm_insertionSort (fun a b : α => a ≤ b) xs
      have hltSort := hperm.countP_eq (fun y => decide (y < x))
      have hleSort := hperm.countP_eq (fun y => decide (y ≤ x))
      symm
      apply getElem?_eq_some_of_count_rank (List.pairwise_insertionSort _ xs)
      · omega
      · omega

/-- **Rank inequalities determine the quickselect value.** Let $L$ be a list over a linear
order, let $k$ be a natural number and let $x$ be an element. Counting entries of $L$ with
multiplicity, if the number of entries less than $x$ is at most $k$ and $k$ is less than the
number of entries at most $x$, then quickselect on $L$ with zero-based rank $k$ returns $x$. -/
theorem quickselect_eq_some_of_count_rank {α : Type u} [LinearOrder α]
    {xs : List α} {k : Nat} {x : α}
    (hlt : xs.countP (fun y => decide (y < x)) ≤ k)
    (hle : k < xs.countP (fun y => decide (y ≤ x))) :
    (quickselect xs k).ret = some x := by
  rw [quickselect_eq_getElem?_insertionSort]
  have hperm := List.perm_insertionSort (fun a b : α => a ≤ b) xs
  apply getElem?_eq_some_of_count_rank (List.pairwise_insertionSort _ xs)
  · simpa only [hperm.countP_eq (fun y => decide (y < x))] using hlt
  · simpa only [hperm.countP_eq (fun y => decide (y ≤ x))] using hle

private theorem choose_two_add_self (n : Nat) :
    n.choose 2 + n = (n + 1).choose 2 := by
  simpa [Nat.choose_one_right, Nat.add_comm, Nat.succ_eq_add_one] using
    (Nat.choose_succ_succ n 1).symm

private theorem recursive_cost_le_choose (m n : Nat) (h : m ≤ n) :
    m.choose 2 + n ≤ (n + 1).choose 2 := by
  have hmono : m.choose 2 ≤ n.choose 2 := Nat.choose_le_choose 2 h
  have hsum := choose_two_add_self n
  omega

/-- **Worst-case comparison bound for quickselect.** For every list $L$ over a linear order, of
length $n$, and every natural number $k$, quickselect on $L$ with rank $k$ makes at most
$n(n-1)/2$ comparisons. -/
theorem quickselect_time (xs : List α) (k : Nat) :
    (quickselect xs k).time ≤ xs.length * (xs.length - 1) / 2 := by
  have loop_time : ∀ (fuel : Nat) (ys : List α) (rank : Nat), ys.length ≤ fuel →
      (quickselect.loop fuel ys rank).time ≤ ys.length.choose 2 := by
    intro fuel
    induction fuel with
    | zero =>
        intro ys rank hlen
        cases ys with
        | nil => simp [quickselect.loop]
        | cons y ys => simp at hlen
    | succ fuel ih =>
        intro ys rank hlen
        cases ys with
        | nil => simp [quickselect.loop]
        | cons pivot tail =>
            have htail : tail.length ≤ fuel := by
              simpa only [List.length_cons, Nat.succ_le_succ_iff] using hlen
            generalize hparts : (partition3 pivot tail).ret = parts
            have hpartsLength := partition3_length pivot tail
            rw [hparts] at hpartsLength
            have hbelowFuel : parts.below.length ≤ fuel := by omega
            have haboveFuel : parts.above.length ≤ fuel := by omega
            by_cases hbelowRank : rank < parts.below.length
            · have hrecursiveTime := ih parts.below rank hbelowFuel
              have hrecursiveBound := recursive_cost_le_choose parts.below.length
                tail.length (by omega)
              simp only [quickselect.loop, time_bind, hparts,
                partition3_time, hbelowRank, ↓reduceIte, List.length_cons]
              omega
            · by_cases hblockRank :
                  rank < parts.below.length + parts.equal.length + 1
              · simp [quickselect.loop, hparts, hbelowRank, hblockRank,
                  partition3_time]
                have hsum := choose_two_add_self tail.length
                omega
              · have hrecursiveTime := ih parts.above
                    (rank - (parts.below.length + parts.equal.length + 1)) haboveFuel
                have hrecursiveBound := recursive_cost_le_choose parts.above.length
                  tail.length (by omega)
                simp only [quickselect.loop, time_bind, hparts,
                  partition3_time, hbelowRank, hblockRank, ↓reduceIte, List.length_cons]
                omega
  rw [← Nat.choose_two_right]
  by_cases hk : k < xs.length
  · simpa [quickselect, hk] using
      loop_time xs.length xs k (Nat.le_refl _)
  · simp [quickselect, hk]

end Cslib.Algorithms.Lean.TimeM
