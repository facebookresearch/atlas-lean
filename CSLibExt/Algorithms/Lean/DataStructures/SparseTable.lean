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

/-- **Sparse table.** A sparse table over a type $\alpha$ consists of an array of elements of
$\alpha$, called its data, and an array of arrays of elements of $\alpha$, called its levels.

The intended meaning is that level $k$ stores the minima of the length-$2^k$ slices of the data;
data and levels are stored as arrays so that entry lookup is random access. Arbitrary values need
not relate data and levels at all; validity ties every stored level to this specification, tables
produced by the construction are valid, and query correctness is stated for valid tables. -/
structure SparseTable (α : Type u) where
  data : Array α
  levels : Array (Array α)

namespace SparseTable

/-- **Option minimum.** For a type $\alpha$ with a minimum operation, the option minimum extends
$\min$ to optional values (elements of $\alpha$ or none): on two elements $a, b$ of $\alpha$ it
returns $\min(a, b)$, and none is a neutral element on either side. -/
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

/-- **Idempotence of the option minimum.** For every linearly ordered type $\alpha$ and every
optional value $a$ (an element of $\alpha$ or none), the option minimum of $a$ with itself is $a$.

This is what lets two overlapping query intervals count their overlap twice. -/
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
**Levels of a sparse table.** For a list $a$ over a type with a minimum operation $\min$, the
levels of $a$ are defined recursively: level $0$ is $a$, and if level $k$ is
$\ell = (\ell_0, \dots, \ell_{m-1})$, then level $k + 1$ is the list of the values
$\min(\ell_i, \ell_{i+2^k})$ for $0 \le i < m - 2^k$ (empty when $m \le 2^k$).

Over a linear order, element $i$ of level $k$ is the minimum of the $2^k$ consecutive elements
of $a$ starting at index $i$, and only start indices whose interval fits in $a$ get an element.
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

/-- **Length of a level.** For a list $a$ of length $n$ over a type with a minimum operation
and a natural number $k$, level $k$ of $a$ has length $\max(n + 1 - 2^k, 0)$: one element for
each start index $i$ with $i + 2^k \le n$. -/
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

/-- **Levels hold interval minima.** Let $a = (a_0, \dots, a_{n-1})$ be a list over a linearly
ordered type, and let $k$ and $i$ be natural numbers with $i + 2^k \le n$. Then level $k$ of $a$
has an element at index $i$, and it equals $\min(a_i, a_{i+1}, \dots, a_{i+2^k-1})$. -/
theorem getElem?_level {α : Type u} [LinearOrder α] (a : List α) (k i : Nat)
    (h : i + 2 ^ k ≤ a.length) :
    (level a k)[i]? = ((a.drop i).take (2 ^ k)).min? := by
  rw [getElem?_level_rangeMin a k i h, rangeMin_eq_min?]

/-- **Next level of a sparse table row.** For a type with a minimum operation, an array
$(r_0, \dots, r_{n-1})$ and a natural number $k$, the next level is the array of length
$n - 2^k$ (empty when $2^k \ge n$) whose entry $i$ is $\min(r_i, r_{i + 2^k})$.

The construction of a sparse table computes each level once from the previous one this way. -/
def nextLevel {α : Type u} [Min α] (row : Array α) (k : Nat) : Array α :=
  Array.zipWith min row (row.extract (2 ^ k) row.size)

theorem toList_nextLevel {α : Type u} [Min α] (row : Array α) (k : Nat) :
    (nextLevel row k).toList =
      List.zipWith min row.toList (row.toList.drop (2 ^ k)) := by
  have hlen : (row.toList.drop (2 ^ k)).length = row.size - 2 ^ k := by
    rw [List.length_drop, Array.length_toList]
  rw [nextLevel, Array.toList_zipWith, Array.toList_extract, List.extract_eq_take_drop,
    List.take_of_length_le (Nat.le_of_eq hlen)]

/-- **One step of the sparse-table construction.** Work over a type with a minimum operation
$\min$. Given a pair $(r, L)$ of a current row $r$ (an array of length $|r|$) and an array $L$
of the rows recorded so far, and a natural number $k$, the build step returns the pair
$(r', L')$, where $L'$ is $L$ with $r$ appended at the end, and $r'$ is the array whose
entry $i$ is $\min(r_i, r_{i+2^k})$ for each $i$ with $i + 2^k < |r|$. -/
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

/-- **Building a sparse table.** For a list $a$ of length $n$ over a type with a minimum
operation $\min$, the sparse table built from $a$ has data $a$ and
$\lfloor \log_2 n \rfloor + 1$ stored rows, where $\lfloor \log_2 0 \rfloor$ is taken to be $0$.
The rows are produced by iterating the build step for $k = 0, 1, \dots, \lfloor \log_2 n \rfloor$,
starting from the current row $a$ and no recorded rows. So row $0$ is $a$, and entry $i$ of
row $k + 1$ is $\min(x_i, x_{i+2^k})$, where $x$ is row $k$ and $i + 2^k$ is less than the
length of $x$. Each row is computed once, from its predecessor. -/
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

/-- **Valid sparse table.** A sparse table over a type with a minimum operation, whose data is a
list $a$ of length $n$, is valid when it has exactly $m + 1$ levels, where
$m = \lfloor \log_2 n \rfloor$ for $n \ge 1$ and $m = 0$ for $n = 0$, and for each $k \le m$ its
level $k$ is the list $L_k$ defined by $L_0 = a$ and, for $x = L_j$, $L_{j+1}$ is the list of
length $|x| - 2^j$ (empty when $2^j \ge |x|$) whose entry $i$ is $\min(x_i, x_{i + 2^j})$. For a
linear order, $L_k$ is the list of minima of the length-$2^k$ slices of $a$.

Tables produced by the construction are valid, an arbitrary value such as data $(1)$ with the
single level $(99)$ is not, and query correctness is stated only for valid tables. -/
def Valid {α : Type u} [Min α] (t : SparseTable α) : Prop :=
  t.levels.toList.map Array.toList =
    (List.range (Nat.log2 t.data.toList.length + 1)).map (level t.data.toList)

/-- **Built sparse tables are valid.** For every list $a$ over a type with a minimum operation,
the sparse table built from $a$ is valid: its stored rows are exactly the levels
$0, 1, \dots, \lfloor \log_2 n \rfloor$ of $a$, in this order, where $n$ is the length of $a$
and $\lfloor \log_2 0 \rfloor$ is taken to be $0$. -/
theorem build_valid {α : Type u} [Min α] (a : List α) : (build a).Valid := by
  simp [Valid, build_levels_toList_map]

/-- **Sparse-table entries.** For a sparse table $t$ and natural numbers $k$ and $i$, the entry
of $t$ at row $k$ and index $i$ is element $i$ of the $k$-th stored row of $t$ (both counted
from $0$) when $t$ has a $k$-th row and that row has an element at index $i$; otherwise the
entry is undefined. Both lookups are random-access array lookups. -/
def entry {α : Type u} (t : SparseTable α) (k i : Nat) : Option α :=
  t.levels[k]?.bind (fun row => row[i]?)

/-- **Rows of a valid sparse table are its levels.** Let $t$ be a valid sparse table over a type
with a minimum operation, with data $d$ of length $n$, and let $k \le \lfloor \log_2 n \rfloor$,
where $\lfloor \log_2 0 \rfloor$ is taken to be $0$. Then for every index $i$, the entry of $t$
at row $k$ and index $i$ is defined exactly when level $k$ of $d$ has an element at index $i$,
and in that case the two are equal. -/
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

/-- **Entries of a built sparse table are interval minima.** Let $a = (a_0, \dots, a_{n-1})$ be
a list over a linearly ordered type, and let $k$ and $i$ be natural numbers with
$i + 2^k \le n$. Then the entry of the sparse table built from $a$ at row $k$ and index $i$ is
defined and equals $\min(a_i, a_{i+1}, \dots, a_{i+2^k-1})$.

No separate bound on $k$ is needed: $i + 2^k \le n$ already implies
$k \le \lfloor \log_2 n \rfloor$. -/
theorem entry_build_eq_min? {α : Type u} [LinearOrder α] (a : List α) (k i : Nat)
    (h : i + 2 ^ k ≤ a.length) :
    (build a).entry k i = ((a.drop i).take (2 ^ k)).min? := by
  rw [entry_build_eq_rangeMin a k i h, rangeMin_eq_min?]

/-- **Entries of a valid sparse table are interval minima.** Let $t$ be a valid sparse table
over a linearly ordered type, with data $d = (d_0, \dots, d_{n-1})$, and let $k$ and $i$ be
natural numbers with $i + 2^k \le n$. Then the entry of $t$ at row $k$ and index $i$ is
defined and equals $\min(d_i, d_{i+1}, \dots, d_{i+2^k-1})$. -/
theorem entry_eq_min?_of_valid {α : Type u} [LinearOrder α] {t : SparseTable α}
    (hValid : t.Valid) (k i : Nat) (h : i + 2 ^ k ≤ t.data.toList.length) :
    t.entry k i = ((t.data.toList.drop i).take (2 ^ k)).min? := by
  have hk : k ≤ Nat.log2 t.data.toList.length := by
    have hpos : 0 < 2 ^ k := Nat.pow_pos (by decide)
    have h2 : 2 ^ k ≤ t.data.toList.length := by omega
    exact (Nat.le_log2 (by omega : t.data.toList.length ≠ 0)).mpr h2
  rw [entry_eq_of_valid hValid hk i, getElem?_level t.data.toList k i h]

/--
**Sparse table range-minimum query.** For a sparse table $t$ over a type with a minimum operation
and natural numbers $l, r$, the query over $[l, r)$ returns none when $r \le l$. Otherwise, with
$k = \lfloor \log_2 (r - l) \rfloor$, it returns the option minimum (the minimum, with none as a
neutral element on either side) of the entries of $t$ at level $k$ and indices $l$ and $r - 2^k$,
in this order, where an entry not stored in $t$ counts as none.
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

/-- **Correctness of queries on valid sparse tables.** Let $t$ be a valid sparse table over a
linearly ordered type whose data is the list $(a_0, \dots, a_{n-1})$, and let $l, r$ be natural
numbers with $r \le n$. Then the range-minimum query over $[l, r)$ on $t$ returns the minimum of
the slice $(a_l, \dots, a_{r-1})$ (none when $r \le l$, where the slice is empty).

Only the premise $r \le n$ is needed: for reversed bounds $r \le l$ both sides are none. -/
theorem query_eq_of_valid {α : Type u} [LinearOrder α] {t : SparseTable α}
    (hValid : t.Valid) {l r : Nat} (hr : r ≤ t.data.toList.length) :
    t.query l r = ((t.data.toList.drop l).take (r - l)).min? := by
  rw [query_rangeMin_of_valid hValid hr, rangeMin_eq_min?]

private theorem query_build_all_rangeMin {α : Type u} [LinearOrder α] (a : List α) :
    (build a).query 0 a.length = rangeMin a := by
  have h := query_rangeMin_of_valid (build_valid a) (t := build a) (l := 0)
    (r := a.length) (by simpa using Nat.le_refl a.length)
  simpa using h

/-- **Correctness of sparse table queries.** Let $a = (a_0, \dots, a_{n-1})$ be a list over a
linearly ordered type and let $l, r$ be natural numbers with $r \le n$. Then the range-minimum
query over $[l, r)$ on the sparse table built from $a$ returns the minimum of the slice
$(a_l, \dots, a_{r-1})$ (none when $r \le l$, where the slice is empty).

No ordering premise $l \le r$ is needed. -/
theorem query_build {α : Type u} [LinearOrder α] (a : List α) {l r : Nat}
    (hr : r ≤ a.length) :
    (build a).query l r = ((a.drop l).take (r - l)).min? := by
  have h := query_eq_of_valid (build_valid a) (t := build a) (l := l) (r := r)
    (by simpa using hr)
  simpa using h

/-- **Whole-range sparse table query.** For every list $a$ of length $n$ over a linearly ordered
type, the range-minimum query over $[0, n)$ on the sparse table built from $a$ returns the
minimum of $a$ (none when $a$ is empty). -/
theorem query_build_all {α : Type u} [LinearOrder α] (a : List α) :
    (build a).query 0 a.length = a.min? := by
  rw [query_build_all_rangeMin, rangeMin_eq_min?]

end SparseTable

end Cslib.Algorithms.Lean
