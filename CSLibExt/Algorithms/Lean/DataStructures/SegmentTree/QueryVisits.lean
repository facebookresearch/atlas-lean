/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.SegmentTree
public import Mathlib.Data.Nat.Log

/-!
# Segment-tree query and update costs

The instrumented call traces record each invocation, including calls that return immediately.
A descending call performs one addition, and no terminal call performs an addition. The costs
count neither evaluation of cached aggregates during construction nor allocation or copying.
-/

@[expose] public section

namespace Cslib.Algorithms.Lean.SegmentTree

universe u

variable {α : Type u}

/-- **Height of a segment tree.** The height is zero on the empty tree and on a leaf;
at an internal node it is one plus the larger of its children's heights. -/
def height : SegmentTree α → Nat
  | .empty | .leaf _ => 0
  | .node _ _ left right => max left.height right.height + 1

/-- **Exact height of a built segment tree.** The tree built from a list of length $n$ over
an additive monoid has height `Nat.clog 2 n`, the ceiling of the base-two logarithm for
$n > 0$. On the empty list the height and the natural-number ceiling logarithm are zero. -/
theorem height_build [AddMonoid α] (xs : List α) : (build xs).height = Nat.clog 2 xs.length := by
  induction hn : xs.length using Nat.strongRecOn generalizing xs with
  | _ n ih =>
    cases xs with
    | nil => rw [← hn, build, height, List.length_nil, Nat.clog_zero_right]
    | cons x xs =>
      cases xs with
      | nil => rw [← hn, build, height, List.length_cons, List.length_nil, Nat.clog_one_right]
      | cons y ys =>
        let zs := x :: y :: ys
        have hlen : zs.length = n := hn
        have hn₂ : 2 ≤ n := by simp only [zs, List.length_cons] at hlen; omega
        have hl : (zs.take (zs.length / 2)).length = n / 2 := by
          rw [List.length_take, hlen, min_eq_left (by omega)]
        have hr : (zs.drop (zs.length / 2)).length = (n + 2 - 1) / 2 := by
          rw [List.length_drop, hlen]
          omega
        have hlt : (zs.take (zs.length / 2)).length < n := by rw [hl]; omega
        have hrt : (zs.drop (zs.length / 2)).length < n := by rw [hr]; omega
        have hmono : Nat.clog 2 (n / 2) ≤ Nat.clog 2 ((n + 2 - 1) / 2) :=
          Nat.clog_mono_right _ (by omega)
        rw [build, height]
        change max (build (zs.take (zs.length / 2))).height
          (build (zs.drop (zs.length / 2))).height + 1 = Nat.clog 2 n
        rw [ih _ hlt _ rfl, ih _ hrt _ rfl, hl, hr, max_eq_right hmono,
          Nat.clog_of_two_le (by decide : 1 < 2) hn₂]

/-- **Call trace for a segment-tree operation.** A trace records an invocation at its root.
It can stop at an empty tree or a pruned internal node (`stop`), stop at a `leaf`, descend
into `one` child (with `true` for the left child), or descend into `both` children in order. -/
inductive CallTrace where
  | stop
  | leaf
  | one (goLeft : Bool) (child : CallTrace)
  | both (left right : CallTrace)
  deriving DecidableEq

/-- **Visits at a given depth.** Count the invocations in a call trace at depth $d$,
with the starting invocation at depth zero. A call on the empty tree is an invocation,
not a stored node. -/
def CallTrace.visitsAt (trace : CallTrace) (d : Nat) : Nat :=
  match d with
  | 0 => 1
  | d + 1 =>
    match trace with
    | .stop | .leaf => 0
    | .one _ child => child.visitsAt d
    | .both left right => left.visitsAt d + right.visitsAt d
termination_by structural d

/-- **Total invocations in a call trace.** Count one for the root call plus all the calls
in its recursive traces. -/
def CallTrace.visits : CallTrace → Nat
  | .stop | .leaf => 1
  | .one _ child => child.visits + 1
  | .both left right => left.visits + right.visits + 1

/-- **Additions in a call trace.** Count one application of the additive monoid operation for
each call that descends, and zero for each terminal call. -/
def CallTrace.adds : CallTrace → Nat
  | .stop | .leaf => 0
  | .one _ child => child.adds + 1
  | .both left right => left.adds + right.adds + 1

/-- **Single path to a leaf.** A call trace is a single path to a leaf if it stops at a leaf
or descends into just one child whose trace is a single path to a leaf. -/
def CallTrace.IsLeafPath : CallTrace → Prop
  | .leaf => True
  | .one _ child => child.IsLeafPath
  | .stop | .both _ _ => False

/-- **Call trace of a range query.** For natural-number endpoints $l,r$, a range query
stops on an empty tree or a leaf. At an internal node of cached size $s$,
it stops if $r\le l$, if $s\le l$, or if $l=0$ and
$s\le r$. Otherwise it calls both children, at bounds $l,r$ on the left and $l-m,r-m$
on the right for left child size $m$, using truncated natural subtraction. -/
def queryTrace : SegmentTree α → Nat → Nat → CallTrace
  | .empty, _, _ => .stop
  | .leaf _, _, _ => .leaf
  | .node _ s left right, l, r =>
      if r ≤ l then .stop
      else if s ≤ l then .stop
      else if l = 0 ∧ s ≤ r then .stop
      else .both (left.queryTrace l r) (right.queryTrace (l - left.size) (r - left.size))

/-- **Evaluation rules for range queries.** For a range query over an additive monoid with
natural-number endpoints $l,r$, the empty-tree rule returns zero.
At a leaf the rule returns its value if $l=0<r$, and zero otherwise.
At a node of cached size $s$ and aggregate $a$, the first satisfied guard among
$r\le l$, $s\le l$, and $l=0\land s\le r$ returns zero, zero, or $a$, respectively.
Otherwise the rule adds the results of the left call at $(l,r)$ and the right call
at $(l-m,r-m)$, where $m$ is the left child's size and subtraction is truncated.
The trace records both subtraces in order in the last case and no children otherwise. -/
inductive QueryEvaluates [AddMonoid α] : SegmentTree α → Nat → Nat → α → CallTrace → Prop
  | empty (l r : Nat) : QueryEvaluates .empty l r 0 .stop
  | leafHit (x : α) {l r : Nat} (h : l = 0 ∧ 0 < r) :
      QueryEvaluates (.leaf x) l r x .leaf
  | leafMiss (x : α) {l r : Nat} (h : ¬(l = 0 ∧ 0 < r)) :
      QueryEvaluates (.leaf x) l r 0 .leaf
  | emptyRange {a : α} {s l r : Nat} {left right : SegmentTree α} (h : r ≤ l) :
      QueryEvaluates (.node a s left right) l r 0 .stop
  | pastEnd {a : α} {s l r : Nat} {left right : SegmentTree α}
      (h : ¬r ≤ l) (hs : s ≤ l) : QueryEvaluates (.node a s left right) l r 0 .stop
  | covered {a : α} {s l r : Nat} {left right : SegmentTree α}
      (h : ¬r ≤ l) (hs : ¬s ≤ l) (hc : l = 0 ∧ s ≤ r) :
      QueryEvaluates (.node a s left right) l r a .stop
  | descend {a x y : α} {s l r : Nat} {left right : SegmentTree α} {lt rt : CallTrace}
      (h : ¬r ≤ l) (hs : ¬s ≤ l) (hc : ¬(l = 0 ∧ s ≤ r))
      (hl : QueryEvaluates left l r x lt)
      (hr : QueryEvaluates right (l - left.size) (r - left.size) y rt) :
      QueryEvaluates (.node a s left right) l r (x + y) (.both lt rt)

/-- **The range-query trace models the query equations.** For every segment tree over an
additive monoid and all natural-number endpoints $l,r$, the actual query result and
computed trace satisfy the query evaluation rules at every recursive call. The caches
need not be valid. -/
theorem query_evaluates [AddMonoid α] (t : SegmentTree α) (l r : Nat) :
    QueryEvaluates t l r (t.query l r) (t.queryTrace l r) := by
  induction t generalizing l r with
  | empty => exact .empty l r
  | leaf x =>
    by_cases h : l = 0 ∧ 0 < r
    · rw [query.eq_2, ite_eq_left h, queryTrace]
      exact .leafHit x h
    · rw [query.eq_2, ite_eq_right h, queryTrace]
      exact .leafMiss x h
  | node a s left right ihl ihr =>
    rw [query.eq_3, queryTrace]
    split_ifs with he hs hc
    · exact .emptyRange he
    · exact .pastEnd he hs
    · exact .covered he hs hc
    · exact .descend he hs hc (ihl l r) (ihr (l - left.size) (r - left.size))

/-- **Call trace of a point update.** A point update at a natural-number index $i$ stops on
an empty tree or at a leaf. It calls just the left child at $i$ when $i<m$ for left size
$m$, and just the right child at $i-m$ otherwise, using truncated natural subtraction.
The trace does not depend on the replacement value. There is no out-of-range guard at
internal nodes. -/
def updateTrace : SegmentTree α → Nat → CallTrace
  | .empty, _ => .stop
  | .leaf _, _ => .leaf
  | .node _ _ left right, i =>
      if i < left.size then .one true (left.updateTrace i)
      else .one false (right.updateTrace (i - left.size))

/-- **Evaluation rules for point updates.** Over an additive monoid, an update at a natural-number
index $i$ with replacement value $y$ leaves the empty tree unchanged and replaces a
leaf's value with $y$ exactly when the local index is zero. At an internal node it calls
just the left child at $i$ if $i<m$, otherwise just the right child at $i-m$, where $m$
is the left size and subtraction is truncated. The trace records the selected child.
The result retains the other child and the cached size, and caches the new left aggregate
plus the new right aggregate, in that order. -/
inductive UpdateEvaluates [AddMonoid α] :
    SegmentTree α → Nat → α → SegmentTree α → CallTrace → Prop
  | empty (i : Nat) (y : α) : UpdateEvaluates .empty i y .empty .stop
  | leafHit (x y : α) {i : Nat} (h : i = 0) : UpdateEvaluates (.leaf x) i y (.leaf y) .leaf
  | leafMiss (x y : α) {i : Nat} (h : i ≠ 0) : UpdateEvaluates (.leaf x) i y (.leaf x) .leaf
  | left {a y : α} {s i : Nat} {left right left' : SegmentTree α} {trace : CallTrace}
      (h : i < left.size) (rec : UpdateEvaluates left i y left' trace) :
      UpdateEvaluates (.node a s left right) i y
        (.node (left'.agg + right.agg) s left' right) (.one true trace)
  | right {a y : α} {s i : Nat} {left right right' : SegmentTree α} {trace : CallTrace}
      (h : ¬i < left.size) (rec : UpdateEvaluates right (i - left.size) y right' trace) :
      UpdateEvaluates (.node a s left right) i y
        (.node (left.agg + right'.agg) s left right') (.one false trace)

/-- **The point-update trace models the update equations.** For every segment tree over an
additive monoid, every natural-number index $i$, and every replacement value $y$ in the
monoid, the actual update result and computed trace satisfy the update evaluation rules
at every recursive call. No cache validity or in-range condition is required. -/
theorem update_evaluates [AddMonoid α] (t : SegmentTree α) (i : Nat) (y : α) :
    UpdateEvaluates t i y (t.update i y) (t.updateTrace i) := by
  induction t generalizing i with
  | empty => exact .empty i y
  | leaf x =>
    by_cases h : i = 0
    · rw [update.eq_2, ite_eq_left h, updateTrace]
      exact .leafHit x y h
    · rw [update.eq_2, ite_eq_right h, updateTrace]
      exact .leafMiss x y h
  | node a s left right ihl ihr =>
    rw [update.eq_3, updateTrace]
    split_ifs with h
    · exact .left h (ihl i)
    · exact .right h (ihr (i - left.size))

/-- An endpoint lies strictly inside the segment of size `s` rather than on its boundary. -/
private def interior (s p : Nat) : Nat := if 0 < p ∧ p < s then 1 else 0

private def boundaries (s l r : Nat) : Nat := interior s l + interior s r

private theorem interior_split (m n p : Nat) :
    interior m p + interior n (p - m) ≤ interior (m + n) p := by
  unfold interior
  split_ifs <;> omega

private theorem boundaries_split (m n l r : Nat) :
    boundaries m l r + boundaries n (l - m) (r - m) ≤ boundaries (m + n) l r := by
  have hl := interior_split m n l
  have hr := interior_split m n r
  unfold boundaries
  omega

private theorem boundaries_le_two (s l r : Nat) : boundaries s l r ≤ 2 := by
  unfold boundaries interior
  split_ifs <;> omega

private theorem boundaries_pos {s l r : Nat} (he : ¬r ≤ l) (hs : ¬s ≤ l)
    (hc : ¬(l = 0 ∧ s ≤ r)) : 0 < boundaries s l r := by
  unfold boundaries interior
  split_ifs <;> omega

-- A call can descend only if an endpoint is interior. Splitting never duplicates an
-- interior endpoint, and an endpoint exactly on the split disappears from the potential.
private theorem QueryEvaluates.visitsAt_succ_le [AddMonoid α]
    {t : SegmentTree α} {l r : Nat} {x : α} {trace : CallTrace}
    (ev : QueryEvaluates t l r x trace) (ht : t.Valid) (d : Nat) :
    trace.visitsAt (d + 1) ≤ 2 * boundaries t.size l r := by
  induction ev generalizing d with
  | empty | leafHit | leafMiss | emptyRange | pastEnd | covered =>
    simp only [CallTrace.visitsAt, Nat.zero_le]
  | @descend a x y s l r left right lt rt he hs hc _ _ ihl ihr =>
    cases ht with
    | node hLeft hRight =>
      change lt.visitsAt d + rt.visitsAt d ≤ 2 * boundaries (left.size + right.size) l r
      cases d with
      | zero =>
        have hp := boundaries_pos he hs hc
        simp only [CallTrace.visitsAt]
        omega
      | succ d =>
        have hl := ihl hLeft d
        have hr := ihr hRight d
        have hsplit := boundaries_split left.size right.size l r
        omega

private theorem QueryEvaluates.totals [AddMonoid α]
    {t : SegmentTree α} {l r : Nat} {x : α} {trace : CallTrace}
    (ev : QueryEvaluates t l r x trace) (ht : t.Valid) :
    trace.adds ≤ boundaries t.size l r * t.height ∧ trace.visits = 2 * trace.adds + 1 := by
  induction ev with
  | empty | leafHit | leafMiss | emptyRange | pastEnd | covered =>
    simp only [CallTrace.adds, CallTrace.visits, Nat.zero_le, Nat.mul_zero, Nat.zero_add, and_self]
  | @descend a x y s l r left right lt rt he hs hc _ _ ihl ihr =>
    cases ht with
    | node hLeft hRight =>
      obtain ⟨hl, hcl⟩ := ihl hLeft
      obtain ⟨hr, hcr⟩ := ihr hRight
      have hp := boundaries_pos he hs hc
      let h := max left.height right.height
      have hadds : lt.adds + rt.adds ≤ boundaries (left.size + right.size) l r * h := calc
        _ ≤ boundaries left.size l r * left.height +
            boundaries right.size (l - left.size) (r - left.size) * right.height :=
          Nat.add_le_add hl hr
        _ ≤ boundaries left.size l r * h +
            boundaries right.size (l - left.size) (r - left.size) * h :=
          Nat.add_le_add (Nat.mul_le_mul_left _ (le_max_left _ _))
            (Nat.mul_le_mul_left _ (le_max_right _ _))
        _ = (boundaries left.size l r +
            boundaries right.size (l - left.size) (r - left.size)) * h :=
          (Nat.add_mul ..).symm
        _ ≤ _ := Nat.mul_le_mul_right h (boundaries_split left.size right.size l r)
      constructor
      · change lt.adds + rt.adds + 1 ≤ boundaries (left.size + right.size) l r * (h + 1)
        rw [Nat.mul_add, Nat.mul_one]
        omega
      · simp only [CallTrace.adds, CallTrace.visits]
        omega

private theorem UpdateEvaluates.path [AddMonoid α]
    {t : SegmentTree α} {i : Nat} {y : α} {t' : SegmentTree α} {trace : CallTrace}
    (ev : UpdateEvaluates t i y t' trace) (ht : t.Valid) (hi : i < t.size) :
    trace.IsLeafPath ∧ trace.adds ≤ t.height ∧ trace.visits = trace.adds + 1 := by
  induction ev with
  | empty => simp [size] at hi
  | leafHit | leafMiss => exact ⟨trivial, Nat.le_refl _, rfl⟩
  | @left a y s i left right left' trace h _ ih =>
    cases ht with
    | node hLeft hRight =>
      obtain ⟨hp, ha, hv⟩ := ih hLeft h
      refine ⟨hp, Nat.succ_le_succ (ha.trans (le_max_left _ _)), ?_⟩
      simp only [CallTrace.visits, CallTrace.adds, hv]
  | @right a y s i left right right' trace h _ ih =>
    cases ht with
    | node hLeft hRight =>
      have hi' : i < left.size + right.size := hi
      have hii : i - left.size < right.size := by omega
      obtain ⟨hp, ha, hv⟩ := ih hRight hii
      refine ⟨hp, Nat.succ_le_succ (ha.trans (le_max_right _ _)), ?_⟩
      simp only [CallTrace.visits, CallTrace.adds, hv]

/-- **Segment-tree queries visit logarithmically many nodes.** For the segment tree built
from a list `xs` of length $n$ over an additive monoid, put $h=\operatorname{clog}_2(n)$
(the ceiling logarithm for $n>0$, and zero at $n=0$). Then:

1. The tree has height $h$, with a leaf at height zero.
2. For all natural bounds $l,r$, the range query invokes at most four calls at any one
   depth, at most $4h+1$ calls in total, and at most $2h$ additions. It returns the
   ordered sum of `((xs.drop l).take (r - l))`, i.e. the half-open range clamped to
   the list. On an empty tree the single invocation visits no stored node.
3. For an in-range index $i<n$ and replacement $y$, the point update follows a single
   root-to-leaf path, with at most $h+1$ calls and $h$ additions. Its leaf list is
   `xs.set i y`.

Calls that return without descending are included; these bounds are not bounds on
allocation, copying, or running time. -/
theorem query_visits_logarithmically [AddMonoid α] (xs : List α) :
    let t := build xs
    let h := Nat.clog 2 xs.length
    t.height = h ∧
      (∀ l r : Nat,
        let trace := t.queryTrace l r
        (∀ d : Nat, trace.visitsAt d ≤ 4) ∧ trace.visits ≤ 4 * h + 1 ∧
          trace.adds ≤ 2 * h ∧ t.query l r = ((xs.drop l).take (r - l)).sum) ∧
      (∀ (i : Nat) (y : α), i < xs.length →
        let trace := t.updateTrace i
        trace.IsLeafPath ∧ trace.visits ≤ h + 1 ∧ trace.adds ≤ h ∧
          (t.update i y).toList = xs.set i y) := by
  refine ⟨height_build xs, ?_, ?_⟩
  · intro l r
    dsimp only
    have ev := query_evaluates (build xs) l r
    have ht := valid_build xs
    obtain ⟨ha, hv⟩ := ev.totals ht
    have hadd : ((build xs).queryTrace l r).adds ≤ 2 * Nat.clog 2 xs.length := by
      rw [height_build] at ha
      exact ha.trans (Nat.mul_le_mul_right _ (boundaries_le_two _ _ _))
    refine ⟨?_, ?_, hadd, query_build xs l r⟩
    · intro d
      cases d with
      | zero => change 1 ≤ 4; decide
      | succ d =>
        exact (ev.visitsAt_succ_le ht d).trans (Nat.mul_le_mul_left 2 (boundaries_le_two _ _ _))
    · omega
  · intro i y hi
    dsimp only
    obtain ⟨hp, ha, hv⟩ := (update_evaluates (build xs) i y).path (valid_build xs)
      (by simpa only [size_build] using hi)
    rw [height_build] at ha
    exact ⟨hp, by omega, ha, toList_update_build hi y⟩

end Cslib.Algorithms.Lean.SegmentTree
