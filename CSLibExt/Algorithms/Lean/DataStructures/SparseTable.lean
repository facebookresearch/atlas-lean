/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.List.Basic
public import Mathlib.Order.Defs.LinearOrder

/-!
# Sparse tables

A sparse table answers range-minimum queries over a static list. The operation must be
idempotent so that two overlapping intervals can jointly cover a query interval: the overlap
is counted twice, and idempotence absorbs the double count. We use `min` over a linear
order, the simplest idempotent operation; idempotence is `min_self`.

Level `k` of the table stores, at each start index `i` with `i + 2 ^ k ≤ n`, the minimum of
the length-`2 ^ k` slice starting at `i`; level `k + 1` combines adjacent level-`k` entries
against the level dropped by `2 ^ k`. The list function `level` states this specification,
while the built table stores its levels in an `Array (Array α)` so that `entry` is random
access, and `build` computes each level once from the single retained previous row. The
built table has `Nat.log2 n + 1` levels. A query over `[l, r)` with `k = Nat.log2 (r - l)`
returns the minimum of the two length-`2 ^ k` slices starting at `l` and at `r - 2 ^ k`,
which overlap and cover `[l, r)`. Slice minima in the public specification are the
canonical `List.min?` (`none` for the empty slice), so an empty query interval returns
`none`; internally the proofs use a private right-fold minimum that is proved equal to
`List.min?` and is not exported. Queries are proved correct whenever `r ≤ n`,
including reversed bounds `r ≤ l`, where both the query and the slice minimum
are `none`.
No complexity bounds are proved; the model carries no cost instrumentation.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean

universe u

/-- A sparse table over `α`: the underlying data together with its levels of interval
minima, stored as arrays so that entry lookup is random access. The list-level function
`level`, together with `List.min?` of slices of `data.toList`, is the specification.
Arbitrary values of this type need not relate `data` and `levels` at all; the
representation invariant `Valid` ties every stored level to `level data.toList`,
`build` produces valid tables, and query correctness is stated for valid tables. -/
structure SparseTable (α : Type u) where
  data : Array α
  levels : Array (Array α)

namespace SparseTable

/-- Minimum on `Option`, with `none` as the neutral element. -/
def omin {α : Type u} [Min α] : Option α → Option α → Option α
  | none, b => b
  | some a, none => some a
  | some a, some b => some (min a b)

theorem omin_none_left {α : Type u} [Min α] (b : Option α) : omin none b = b := by
  cases b <;> rfl

theorem omin_none_right {α : Type u} [Min α] (a : Option α) : omin a none = a := by
  cases a <;> rfl

theorem omin_some_some {α : Type u} [Min α] (a b : α) :
    omin (some a) (some b) = some (min a b) :=
  rfl

theorem omin_comm {α : Type u} [LinearOrder α] (a b : Option α) :
    omin a b = omin b a := by
  cases a <;> cases b <;> simp [omin, min_comm]

theorem omin_assoc {α : Type u} [LinearOrder α] (a b c : Option α) :
    omin (omin a b) c = omin a (omin b c) := by
  cases a <;> cases b <;> cases c <;> simp [omin, min_assoc]

/-- `omin` is idempotent; this is what lets overlapping query intervals double-count. -/
theorem omin_self {α : Type u} [LinearOrder α] (a : Option α) : omin a a = a := by
  cases a <;> simp [omin]

/-- Internal right-fold list minimum as an `Option` (`none` on the empty
list), used only in proofs; the public specification uses the canonical
`List.min?`, to which this is proved equal below. Not exported. -/
private def rangeMin {α : Type u} [Min α] : List α → Option α
  | [] => none
  | x :: xs => omin (some x) (rangeMin xs)

@[simp]
private theorem rangeMin_nil {α : Type u} [Min α] : rangeMin ([] : List α) = none :=
  rfl

@[simp]
private theorem rangeMin_cons {α : Type u} [Min α] (x : α) (xs : List α) :
    rangeMin (x :: xs) = omin (some x) (rangeMin xs) :=
  rfl

/-- The minimum of an append is `omin` of the two minima. -/
private theorem rangeMin_append {α : Type u} [LinearOrder α] (xs ys : List α) :
    rangeMin (xs ++ ys) = omin (rangeMin xs) (rangeMin ys) := by
  induction xs with
  | nil => simp only [List.nil_append, rangeMin_nil, omin_none_left]
  | cons x xs ih =>
      simp only [List.cons_append, rangeMin_cons, ih, omin_assoc]

/-- A nonempty list has a minimum. -/
private theorem rangeMin_eq_some {α : Type u} [Min α] {xs : List α} (h : xs ≠ []) :
    ∃ x, rangeMin xs = some x := by
  cases xs with
  | nil => exact (h rfl).elim
  | cons x xs =>
      cases hrm : rangeMin xs with
      | none => exact ⟨x, by rw [rangeMin_cons, hrm, omin_none_right]⟩
      | some m => exact ⟨min x m, by rw [rangeMin_cons, hrm, omin_some_some]⟩

/-- The internal fold minimum agrees with the canonical `List.min?`. -/
private theorem rangeMin_eq_min? {α : Type u} [LinearOrder α] (xs : List α) :
    rangeMin xs = xs.min? := by
  haveI : Std.Associative (min : α → α → α) := ⟨fun a b c => min_assoc a b c⟩
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      rw [rangeMin_cons, ih, List.min?_cons]
      cases xs.min? <;> rfl

private theorem slice_split {α : Type u} {a : List α} {x y z : Nat}
    (hxy : x ≤ y) (hyz : y ≤ z) (hz : z ≤ a.length) :
    (a.drop x).take (z - x) = (a.drop x).take (y - x) ++ (a.drop y).take (z - y) := by
  have hdrop : (a.drop x).drop (y - x) = a.drop y := by
    rw [List.drop_drop, Nat.add_sub_cancel' hxy]
  have hlen : ((a.drop x).take (y - x)).length = y - x := by
    rw [List.length_take, List.length_drop]
    omega
  conv_lhs => rw [← List.take_append_drop (y - x) (a.drop x), hdrop]
  rw [List.take_append, hlen,
    List.take_of_length_le (show ((a.drop x).take (y - x)).length ≤ z - x by
      rw [hlen]; omega),
    show z - x - (y - x) = z - y by omega]

/-- Two overlapping intervals sharing the middle block `M` jointly have the union's minimum. -/
private theorem rangeMin_overlap {α : Type u} [LinearOrder α] (P M S : List α) :
    omin (rangeMin (P ++ M)) (rangeMin (M ++ S)) = rangeMin (P ++ M ++ S) := by
  calc
    omin (rangeMin (P ++ M)) (rangeMin (M ++ S))
        = omin (omin (rangeMin P) (rangeMin M)) (omin (rangeMin M) (rangeMin S)) := by
          rw [rangeMin_append, rangeMin_append]
    _ = omin (rangeMin P) (omin (rangeMin M) (omin (rangeMin M) (rangeMin S))) :=
          omin_assoc _ _ _
    _ = omin (rangeMin P) (omin (omin (rangeMin M) (rangeMin M)) (rangeMin S)) := by
          rw [← omin_assoc (rangeMin M) (rangeMin M) (rangeMin S)]
    _ = omin (rangeMin P) (omin (rangeMin M) (rangeMin S)) := by
          rw [omin_self]
    _ = omin (omin (rangeMin P) (rangeMin M)) (rangeMin S) := (omin_assoc _ _ _).symm
    _ = rangeMin (P ++ M ++ S) := by
          rw [rangeMin_append, rangeMin_append]

/--
Level `k` of the sparse table over `a`: entry `i` is the minimum of the length-`2 ^ k`
slice of `a` starting at `i`. Only starts whose interval fits in `a` get an entry.
-/
def level {α : Type u} [Min α] (a : List α) : Nat → List α
  | 0 => a
  | k + 1 => List.zipWith min (level a k) ((level a k).drop (2 ^ k))

theorem level_zero {α : Type u} [Min α] (a : List α) : level a 0 = a :=
  rfl

theorem level_succ {α : Type u} [Min α] (a : List α) (k : Nat) :
    level a (k + 1) = List.zipWith min (level a k) ((level a k).drop (2 ^ k)) :=
  rfl

private theorem two_pow_succ (k : Nat) : (2 : Nat) ^ (k + 1) = 2 ^ k + 2 ^ k := by
  rw [Nat.pow_add]
  show 2 ^ k * 2 = 2 ^ k + 2 ^ k
  omega

/-- Level `k` has one entry per start index whose length-`2 ^ k` interval fits. -/
theorem level_length {α : Type u} [Min α] (a : List α) (k : Nat) :
    (level a k).length = a.length + 1 - 2 ^ k := by
  induction k with
  | zero =>
      show (level a 0).length = a.length + 1 - 2 ^ 0
      rw [level_zero]
      omega
  | succ k ih =>
      show (level a (k + 1)).length = a.length + 1 - 2 ^ (k + 1)
      rw [level_succ, List.length_zipWith, List.length_drop, ih, two_pow_succ]
      have hpos : 0 < 2 ^ k := Nat.pow_pos (by decide)
      omega

/-- An in-range level entry is the minimum of its interval slice. -/
private theorem getElem?_level_rangeMin {α : Type u} [LinearOrder α] (a : List α) (k i : Nat)
    (h : i + 2 ^ k ≤ a.length) :
    (level a k)[i]? = rangeMin ((a.drop i).take (2 ^ k)) := by
  induction k generalizing i with
  | zero =>
      have h0 : (a.drop i)[0]? = a[i]? := by
        rw [List.getElem?_drop]
        simp
      cases hdrop : a.drop i with
      | nil =>
          have hnone : a[i]? = none := by
            rw [← h0, hdrop]
            rfl
          rw [level_zero, hnone]
          simp
      | cons x xs =>
          have hsome : a[i]? = some x := by
            rw [← h0, hdrop]
            rfl
          rw [level_zero, hsome, show (x :: xs).take (2 ^ 0) = [x] from rfl,
            rangeMin_cons, rangeMin_nil, omin_none_right]
  | succ k ih =>
      have h' : i + 2 ^ (k + 1) ≤ a.length := h
      rw [two_pow_succ] at h'
      have hpos : 0 < 2 ^ k := Nat.pow_pos (by decide)
      have h1 : i + 2 ^ k ≤ a.length := by omega
      have h2 : (i + 2 ^ k) + 2 ^ k ≤ a.length := by omega
      have hne1 : (a.drop i).take (2 ^ k) ≠ [] := by
        intro he
        have hlen := congrArg List.length he
        simp only [List.length_take, List.length_drop, List.length_nil] at hlen
        omega
      have hne2 : (a.drop (i + 2 ^ k)).take (2 ^ k) ≠ [] := by
        intro he
        have hlen := congrArg List.length he
        simp only [List.length_take, List.length_drop, List.length_nil] at hlen
        omega
      obtain ⟨x, hx⟩ := rangeMin_eq_some hne1
      obtain ⟨y, hy⟩ := rangeMin_eq_some hne2
      have hsplit := slice_split (a := a) (x := i) (y := i + 2 ^ k)
        (z := i + 2 ^ k + 2 ^ k) (by omega) (by omega) (by omega)
      rw [show i + 2 ^ k + 2 ^ k - i = 2 ^ k + 2 ^ k by omega,
        show i + 2 ^ k - i = 2 ^ k by omega,
        show i + 2 ^ k + 2 ^ k - (i + 2 ^ k) = 2 ^ k by omega] at hsplit
      show (level a (k + 1))[i]? = rangeMin ((a.drop i).take (2 ^ (k + 1)))
      rw [level_succ, List.getElem?_zipWith, List.getElem?_drop,
        Nat.add_comm (2 ^ k) i, ih i h1, ih (i + 2 ^ k) h2, hx, hy, two_pow_succ,
        hsplit, rangeMin_append, hx, hy]
      rfl

/-- An in-range level entry is `List.min?` of its interval slice. -/
theorem getElem?_level {α : Type u} [LinearOrder α] (a : List α) (k i : Nat)
    (h : i + 2 ^ k ≤ a.length) :
    (level a k)[i]? = ((a.drop i).take (2 ^ k)).min? := by
  rw [getElem?_level_rangeMin a k i h, rangeMin_eq_min?]

/-- The next level built from `row`: entry `i` combines entries `i` and `i + 2 ^ k` of
`row`. Computed once from the retained previous row during `build`. -/
def nextLevel {α : Type u} [Min α] (row : Array α) (k : Nat) : Array α :=
  Array.zipWith min row (row.extract (2 ^ k) row.size)

theorem toList_nextLevel {α : Type u} [Min α] (row : Array α) (k : Nat) :
    (nextLevel row k).toList =
      List.zipWith min row.toList (row.toList.drop (2 ^ k)) := by
  have hlen : (row.toList.drop (2 ^ k)).length = row.size - 2 ^ k := by
    rw [List.length_drop, Array.length_toList]
  rw [nextLevel, Array.toList_zipWith, Array.toList_extract, List.extract_eq_take_drop,
    List.take_of_length_le (Nat.le_of_eq hlen)]

/-- One step of the iterative construction: record the current row as the next level and
compute the following row from it. The state is the current row together with the levels
built so far. -/
def buildStep {α : Type u} [Min α] (state : Array α × Array (Array α)) (k : Nat) :
    Array α × Array (Array α) :=
  (nextLevel state.1 k, state.2.push state.1)

private theorem build_fold_spec {α : Type u} [Min α] (a : List α) (t : Nat) :
    (((List.range t).foldl buildStep (a.toArray, #[])).2.toList.map Array.toList =
      (List.range t).map (level a)) ∧
    ((List.range t).foldl buildStep (a.toArray, #[])).1.toList = level a t := by
  induction t with
  | zero =>
      exact ⟨rfl, List.toList_toArray⟩
  | succ t ih =>
      obtain ⟨ihAcc, ihRow⟩ := ih
      rw [List.range_succ, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      constructor
      · show (((List.range t).foldl buildStep (a.toArray, #[])).2.push
            ((List.range t).foldl buildStep (a.toArray, #[])).1).toList.map
            Array.toList = _
        rw [Array.toList_push, List.map_append, ihAcc, List.map_append,
          List.map_cons, List.map_cons, List.map_nil, List.map_nil, ihRow]
      · show (nextLevel ((List.range t).foldl buildStep (a.toArray, #[])).1 t).toList = _
        rw [toList_nextLevel, ihRow, ← level_succ]

/-- Builds the sparse table over `a` with `Nat.log2 a.length + 1` levels. Levels are
built iteratively: a fold threads one retained row through `buildStep`, computing each
level once from its predecessor, and stores the levels in an array. The input array is
bound once (`data`) and shared between level zero and the `data` field. -/
def build {α : Type u} [Min α] (a : List α) : SparseTable α :=
  let data := a.toArray
  let final := (List.range (Nat.log2 a.length + 1)).foldl buildStep (data, #[])
  ⟨data, final.2⟩

@[simp]
theorem build_data_toList {α : Type u} [Min α] (a : List α) :
    (build a).data.toList = a :=
  List.toList_toArray

theorem build_levels_toList_map {α : Type u} [Min α] (a : List α) :
    (build a).levels.toList.map Array.toList =
      (List.range (Nat.log2 a.length + 1)).map (level a) :=
  (build_fold_spec a (Nat.log2 a.length + 1)).1

/-- The representation invariant: every stored level is exactly `level data.toList`,
so a valid table's entries are the interval minima of its own data. Tables built by
`build` are valid (`build_valid`); an arbitrary value such as `⟨#[1], #[#[99]]⟩` is
not, and query correctness below is stated only for valid tables. -/
def Valid {α : Type u} [Min α] (t : SparseTable α) : Prop :=
  t.levels.toList.map Array.toList =
    (List.range (Nat.log2 t.data.toList.length + 1)).map (level t.data.toList)

/-- Tables produced by `build` satisfy the representation invariant. -/
theorem build_valid {α : Type u} [Min α] (a : List α) : (build a).Valid := by
  simp [Valid, build_levels_toList_map]

/-- Entry `i` of level `k`, as an `Option`; `none` when out of range. Both indexes are
array lookups. -/
def entry {α : Type u} (t : SparseTable α) (k i : Nat) : Option α :=
  t.levels[k]?.bind (fun row => row[i]?)

/-- In a valid table, entry `i` of level `k` is the corresponding entry of
`level t.data.toList`. -/
theorem entry_eq_of_valid {α : Type u} [Min α] {t : SparseTable α}
    (hValid : t.Valid) {k : Nat} (hk : k ≤ Nat.log2 t.data.toList.length)
    (i : Nat) :
    t.entry k i = (level t.data.toList k)[i]? := by
  have hklt : k < Nat.log2 t.data.toList.length + 1 := by omega
  have h1 : (t.levels.toList.map Array.toList)[k]? =
      some (level t.data.toList k) := by
    rw [hValid, List.getElem?_map, List.getElem?_range hklt, Option.map_some]
  rw [List.getElem?_map] at h1
  obtain ⟨row, hrow, hrowList⟩ :
      ∃ row, t.levels.toList[k]? = some row ∧
        row.toList = level t.data.toList k := by
    cases h : t.levels.toList[k]? with
    | none =>
        rw [h] at h1
        simp at h1
    | some row =>
        rw [h, Option.map_some] at h1
        exact ⟨row, rfl, Option.some.inj h1⟩
  have h2 : t.levels[k]? = some row := by
    rw [← Array.getElem?_toList]
    exact hrow
  rw [entry, h2]
  show row[i]? = (level t.data.toList k)[i]?
  rw [← Array.getElem?_toList, hrowList]

theorem entry_build {α : Type u} [Min α] (a : List α) {k : Nat}
    (hk : k ≤ Nat.log2 a.length) (i : Nat) :
    (build a).entry k i = (level a k)[i]? := by
  have h := entry_eq_of_valid (build_valid a) (t := build a)
    (by simpa using hk) i
  simpa using h

private theorem entry_build_eq_rangeMin {α : Type u} [LinearOrder α] (a : List α) (k i : Nat)
    (h : i + 2 ^ k ≤ a.length) :
    (build a).entry k i = rangeMin ((a.drop i).take (2 ^ k)) := by
  have hk : k ≤ Nat.log2 a.length := by
    have hpos : 0 < 2 ^ k := Nat.pow_pos (by decide)
    have h2 : 2 ^ k ≤ a.length := by omega
    exact (Nat.le_log2 (by omega : a.length ≠ 0)).mpr h2
  rw [entry_build a hk i, getElem?_level_rangeMin a k i h]

/-- A built table's in-range entry is `List.min?` of its interval slice. The
interval-fit premise alone suffices: it implies `2 ^ k ≤ a.length`, hence the
level bound `k ≤ Nat.log2 a.length`, which is derived internally. -/
theorem entry_build_eq_min? {α : Type u} [LinearOrder α] (a : List α) (k i : Nat)
    (h : i + 2 ^ k ≤ a.length) :
    (build a).entry k i = ((a.drop i).take (2 ^ k)).min? := by
  rw [entry_build_eq_rangeMin a k i h, rangeMin_eq_min?]

/-- A valid table's in-range entry is `List.min?` of its interval slice. -/
theorem entry_eq_min?_of_valid {α : Type u} [LinearOrder α] {t : SparseTable α}
    (hValid : t.Valid) (k i : Nat) (h : i + 2 ^ k ≤ t.data.toList.length) :
    t.entry k i = ((t.data.toList.drop i).take (2 ^ k)).min? := by
  have hk : k ≤ Nat.log2 t.data.toList.length := by
    have hpos : 0 < 2 ^ k := Nat.pow_pos (by decide)
    have h2 : 2 ^ k ≤ t.data.toList.length := by omega
    exact (Nat.le_log2 (by omega : t.data.toList.length ≠ 0)).mpr h2
  rw [entry_eq_of_valid hValid hk i, getElem?_level t.data.toList k i h]

/--
Range-minimum query over `[l, r)`: the minimum of the two length-`2 ^ k` entries starting
at `l` and at `r - 2 ^ k`, where `k = Nat.log2 (r - l)`. Empty intervals give `none`.
-/
def query {α : Type u} [Min α] (t : SparseTable α) (l r : Nat) : Option α :=
  if r ≤ l then none
  else omin (t.entry (Nat.log2 (r - l)) l)
    (t.entry (Nat.log2 (r - l)) (r - 2 ^ (Nat.log2 (r - l))))

private theorem query_rangeMin_of_valid {α : Type u} [LinearOrder α]
    {t : SparseTable α} (hValid : t.Valid) {l r : Nat}
    (hr : r ≤ t.data.toList.length) :
    t.query l r = rangeMin ((t.data.toList.drop l).take (r - l)) := by
  by_cases h : r ≤ l
  · have hEq : r - l = 0 := by omega
    simp [query, h, hEq]
  · unfold query
    rw [ite_eq_right h]
    generalize hk : Nat.log2 (r - l) = k
    have hple : 2 ^ k ≤ r - l := by
      rw [← hk]
      exact Nat.log2_self_le (by omega)
    have hlt : r - l < 2 ^ k + 2 ^ k := by
      have h2 := Nat.lt_log2_self (n := r - l)
      rw [hk, two_pow_succ] at h2
      exact h2
    have hklog : k ≤ Nat.log2 t.data.toList.length := by
      rw [Nat.le_log2 (by omega : t.data.toList.length ≠ 0)]
      omega
    have e1 : t.entry k l = rangeMin ((t.data.toList.drop l).take (2 ^ k)) := by
      rw [entry_eq_of_valid hValid hklog l,
        getElem?_level_rangeMin t.data.toList k l (by omega)]
    have e2 : t.entry k (r - 2 ^ k) =
        rangeMin ((t.data.toList.drop (r - 2 ^ k)).take (2 ^ k)) := by
      rw [entry_eq_of_valid hValid hklog (r - 2 ^ k),
        getElem?_level_rangeMin t.data.toList k (r - 2 ^ k) (by omega)]
    rw [e1, e2]
    have hsplit1 := slice_split (a := t.data.toList) (x := l) (y := r - 2 ^ k)
      (z := l + 2 ^ k) (by omega) (by omega) (by omega)
    have hsplit2 := slice_split (a := t.data.toList) (x := r - 2 ^ k)
      (y := l + 2 ^ k) (z := r) (by omega) (by omega) hr
    have hsplit3 := slice_split (a := t.data.toList) (x := l) (y := l + 2 ^ k)
      (z := r) (by omega) (by omega) hr
    rw [show l + 2 ^ k - l = 2 ^ k by omega] at hsplit1
    rw [show r - (r - 2 ^ k) = 2 ^ k by omega] at hsplit2
    rw [show l + 2 ^ k - l = 2 ^ k by omega] at hsplit3
    rw [hsplit3, hsplit1, hsplit2]
    exact rangeMin_overlap _ _ _

/-- A query on a valid table is `List.min?` of the corresponding list slice.
Only the in-range premise `r ≤ t.data.toList.length` is needed: for reversed
bounds `r ≤ l` both sides are `none`. -/
theorem query_eq_of_valid {α : Type u} [LinearOrder α] {t : SparseTable α}
    (hValid : t.Valid) {l r : Nat} (hr : r ≤ t.data.toList.length) :
    t.query l r = ((t.data.toList.drop l).take (r - l)).min? := by
  rw [query_rangeMin_of_valid hValid hr, rangeMin_eq_min?]

private theorem query_build_all_rangeMin {α : Type u} [LinearOrder α] (a : List α) :
    (build a).query 0 a.length = rangeMin a := by
  have h := query_rangeMin_of_valid (build_valid a) (t := build a) (l := 0)
    (r := a.length) (by simpa using Nat.le_refl a.length)
  simpa using h

/-- A query on a built table is `List.min?` of the corresponding list slice,
with no ordering premise on the bounds. -/
theorem query_build {α : Type u} [LinearOrder α] (a : List α) {l r : Nat}
    (hr : r ≤ a.length) :
    (build a).query l r = ((a.drop l).take (r - l)).min? := by
  have h := query_eq_of_valid (build_valid a) (t := build a) (l := l) (r := r)
    (by simpa using hr)
  simpa using h

/-- A query over the whole array is `List.min?` of the whole list. -/
theorem query_build_all {α : Type u} [LinearOrder α] (a : List α) :
    (build a).query 0 a.length = a.min? := by
  rw [query_build_all_rangeMin, rangeMin_eq_min?]

end SparseTable

end Cslib.Algorithms.Lean
