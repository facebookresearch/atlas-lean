/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.List.Sort
public import Mathlib.Data.List.Range
public import Mathlib.Data.List.Perm.Basic
public import Mathlib.Data.Nat.Log

/-!
# Orthogonal range reporting with range trees

We model the static reporting structures of Demaine, *6.851: Advanced Data Structures*,
Lecture 3, §§3.1–3.2. A list represents occurrences, so coincident input points are retained
with multiplicity. Coordinate zero is queried first and the endpoints are inclusive. A
catalog ordered by the current coordinate uses the cuts `< lower` and `≤ upper`; ties are
never broken by a query endpoint. In the layered base, an occurrence's position in the
penultimate-coordinate order determines its child; the child inherits the parent's order by
the last coordinate, including among ties.

An internal node splits its ordered position interval into floor and ceiling halves. An
ordinary query inspects only the two boundary paths and adjacent subtrees; it uses the
attached next-coordinate index at fully contained nodes. One ordinary coordinate uses a
balanced position tree and a shared ordered array for reporting full subtrees. In two
layered coordinates we search both endpoints in the root last-coordinate catalog, and then
read one precomputed entry per boundary and child. Higher layered dimensions use this as
the final two-coordinate structure.

The output traversal composes continuations without constructing child result lists.
It applies each child continuation once, and its terminal iterator directly reads the
selected array indices in descending order. It prepends each projected reference to the single
output tail, preserving the emitted segment's catalog order, and accounts for one emission
per read and cons. Finalization executes the continuation once and does not recount the list.

The model charges a midpoint probe (one indexed read, a key-oracle evaluation, a comparison,
index arithmetic and fixed call/return control); a visit (endpoint tests, child selection,
continuation construction and application, fixed bookkeeping and at a layered split at most
four indexed position-table reads); and an emission (one indexed read, optional tag projection,
index and count operations, one cons and fixed loop control). The root visit includes the
fixed setup and exit of at most four boundary searches, with fixed-width `log2` as an index
setup primitive; an emit visit includes setup and exit of its output iterator. Key projection
and comparison are external unit-cost oracles. Occupied storage counts static catalog slots,
records and position entries, not point payloads, the key oracle's representation, fixed root
descriptors or empty sentinels; it is not the transient continuation stack or the output list.
No preprocessing, variable-cost oracles, bit-complexity, or Lean evaluator-time bound is asserted.
-/

public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.RangeTree.OrthogonalReporting

universe u v w t r

variable {α : Type u} {β : Type v}

/-- The half-open position interval `[start, start + len)`. -/
structure PositionInterval where
  /-- First position (included when the length is positive). -/
  start : Nat
  /-- Number of positions. -/
  len : Nat
  deriving DecidableEq, Repr

namespace PositionInterval

/-- Exclusive upper endpoint. -/
def stop (i : PositionInterval) : Nat := i.start + i.len

/-- Membership of a position in the half-open interval. -/
def Contains (i : PositionInterval) (p : Nat) : Prop := i.start ≤ p ∧ p < i.stop

/-- The left child; used for splitting intervals of length at least two. -/
private def left (i : PositionInterval) : PositionInterval := ⟨i.start, i.len / 2⟩

/-- The right child; used for splitting intervals of length at least two. -/
private def right (i : PositionInterval) : PositionInterval :=
  ⟨i.start + i.len / 2, i.len - i.len / 2⟩

/-- The least sufficient height fuel, including zero for empty and singleton intervals. -/
private def height (i : PositionInterval) : Nat := Nat.clog 2 i.len

/-- A root can always take `PositionInterval.height` as its fuel. -/
private theorem len_le_pow_height (i : PositionInterval) : i.len ≤ 2 ^ i.height :=
  Nat.le_pow_clog (by decide) i.len

@[simp] private theorem height_empty (s : Nat) : (PositionInterval.mk s 0).height = 0 := by
  simp [height]

@[simp] private theorem height_singleton (s : Nat) : (PositionInterval.mk s 1).height = 0 := by
  simp [height]

/-- The children partition the parent, including for lengths zero and one. -/
private theorem contains_children (i : PositionInterval) (p : Nat) :
    i.Contains p ↔ i.left.Contains p ∨ i.right.Contains p := by
  simp only [Contains, stop, left, right]
  omega

/-- Positions of the left child precede positions of the right child. -/
private theorem left_lt_right {i : PositionInterval} {p q : Nat}
    (hp : i.left.Contains p) (hq : i.right.Contains q) : p < q := by
  simp only [Contains, stop, left, right] at hp hq
  omega

/-- A proper split has two nonempty children, each strictly smaller than the parent. -/
private theorem child_lens {i : PositionInterval} (hi : 2 ≤ i.len) :
    0 < i.left.len ∧ 0 < i.right.len ∧ i.left.len < i.len ∧ i.right.len < i.len := by
  simp only [left, right]
  omega

/-- One level of height fuel suffices for the split, also at lengths zero and one. -/
private theorem child_fuel {i : PositionInterval} {h : Nat} (hi : i.len ≤ 2 ^ (h + 1)) :
    i.left.len ≤ 2 ^ h ∧ i.right.len ≤ 2 ^ h := by
  rw [Nat.pow_succ] at hi
  simp only [left, right]
  omega

end PositionInterval

/-- The action at a visited position interval. -/
private inductive PositionAction where
  /-- The interval has no queried positions. -/
  | skip
  /-- The interval is nonempty and wholly contained in the query. -/
  | emit
  /-- The interval overlaps the query but is not wholly contained. -/
  | split
  deriving DecidableEq, Repr

/-- Classify a node using endpoints alone. A reversed query is empty. -/
private def positionAction (lo hi : Nat) (i : PositionInterval) : PositionAction :=
  if i.len = 0 ∨ hi ≤ lo ∨ hi ≤ i.start ∨ i.stop ≤ lo then .skip
  else if lo ≤ i.start ∧ i.stop ≤ hi then .emit
  else .split

/-- Skipping excludes every position of the intersection. -/
private theorem positionAction_skip {lo hi : Nat} {i : PositionInterval}
    (ha : positionAction lo hi i = .skip) {p : Nat} (hp : i.Contains p) :
    ¬ (lo ≤ p ∧ p < hi) := by
  unfold positionAction at ha
  split at ha
  · rename_i hs
    unfold PositionInterval.Contains PositionInterval.stop at hp
    unfold PositionInterval.stop at hs
    omega
  · split at ha <;> contradiction

/-- Emitting certifies a nonempty interval contained in the query. -/
private theorem positionAction_emit {lo hi : Nat} {i : PositionInterval}
    (ha : positionAction lo hi i = .emit) : 0 < i.len ∧ lo ≤ i.start ∧ i.stop ≤ hi := by
  unfold positionAction at ha
  split at ha
  · contradiction
  · rename_i hs
    split at ha
    · rename_i hf
      omega
    · contradiction

/-- A node that needs a split has at least two positions and contains a query endpoint strictly
in its interior. -/
private theorem positionAction_split {lo hi : Nat} {i : PositionInterval}
    (ha : positionAction lo hi i = .split) :
    2 ≤ i.len ∧ (i.start < lo ∧ lo < i.stop ∨ i.start < hi ∧ hi < i.stop) := by
  unfold positionAction at ha
  split at ha
  · contradiction
  · rename_i hs
    split at ha
    · contradiction
    · rename_i hf
      unfold PositionInterval.stop at hs hf ⊢
      omega

/-- The shared traversal. Only `.split` computes child states and recurses; `.skip` and `.emit`
are terminal. The fuel-zero split fallback is unreachable when `i.len ≤ 2 ^ h`.

For a stored tree, let `σ` be the current node/cursor state and advance it by cached child
links in `downLeft` and `downRight`; no root-to-node path needs to be replayed. -/
private def positionFold {σ α : Type*} (lo hi : Nat)
    (downLeft downRight : σ → PositionInterval → σ)
    (skip emit : σ → PositionInterval → α)
    (join : σ → PositionInterval → α → α → α) : Nat → σ → PositionInterval → α
  | h, state, i =>
    match positionAction lo hi i with
    | .skip => skip state i
    | .emit => emit state i
    | .split =>
      match h with
      | 0 => skip state i
      | k + 1 => join state i
          (positionFold lo hi downLeft downRight skip emit join k (downLeft state i) i.left)
          (positionFold lo hi downLeft downRight skip emit join k (downRight state i) i.right)

/-- Number of node inspections made by `positionFold`, including terminal nodes. -/
def positionVisits (lo hi h : Nat) (i : PositionInterval) : Nat :=
  positionFold lo hi (fun (_ : Unit) _ => ()) (fun _ _ => ())
    (fun _ _ => 1) (fun _ _ => 1) (fun _ _ l r => 1 + l + r) h () i

/-- Even an immediately pruned node is inspected once. -/
private theorem positionVisits_skip {lo hi h : Nat} {i : PositionInterval}
    (ha : positionAction lo hi i = .skip) : positionVisits lo hi h i = 1 := by
  cases h <;> simp [positionVisits, positionFold, ha]

/-- A canonical node is inspected once, without inspecting its descendants. -/
private theorem positionVisits_emit {lo hi h : Nat} {i : PositionInterval}
    (ha : positionAction lo hi i = .emit) : positionVisits lo hi h i = 1 := by
  cases h <;> simp [positionVisits, positionFold, ha]

/-- At zero fuel the root is the only node inspected. -/
private theorem positionVisits_zero (lo hi : Nat) (i : PositionInterval) :
    positionVisits lo hi 0 i = 1 := by
  cases ha : positionAction lo hi i <;> simp [positionVisits, positionFold, ha]

/-- The visit count at a split is the root inspection plus visits to the two children. -/
private theorem positionVisits_split {lo hi h : Nat} {i : PositionInterval}
    (ha : positionAction lo hi i = .split) :
    positionVisits lo hi (h + 1) i =
      1 + positionVisits lo hi h i.left + positionVisits lo hi h i.right := by
  simp [positionVisits, positionFold, ha]

/-- A difference-list version of `positionCover` that prepends the cover to a caller's tail. -/
private def positionCoverAux (lo hi h : Nat) (i : PositionInterval)
    (tail : List PositionInterval) : List PositionInterval :=
  positionFold lo hi (fun (_ : Unit) _ => ()) (fun _ _ => ())
    (fun _ _ => id) (fun _ j => (j :: ·)) (fun _ _ l r => l ∘ r) h () i tail

/-- Emit the wholly contained canonical nodes in left-to-right order. A difference list avoids
copying an already-built prefix at each split. Use fuel `h` such that `i.len ≤ 2 ^ h`. -/
def positionCover (lo hi h : Nat) (i : PositionInterval) : List PositionInterval :=
  positionCoverAux lo hi h i []

private theorem positionCoverAux_append (lo hi h : Nat) (i : PositionInterval)
    (tail : List PositionInterval) :
    positionCoverAux lo hi h i tail = positionCover lo hi h i ++ tail := by
  induction h generalizing i tail with
  | zero =>
    cases ha : positionAction lo hi i <;>
      simp [positionCover, positionCoverAux, positionFold, ha]
  | succ h ih =>
    cases ha : positionAction lo hi i with
    | skip => simp [positionCover, positionCoverAux, positionFold, ha]
    | emit => simp [positionCover, positionCoverAux, positionFold, ha]
    | split =>
      have step (xs : List PositionInterval) :
          positionCoverAux lo hi (h + 1) i xs =
            positionCoverAux lo hi h i.left (positionCoverAux lo hi h i.right xs) := by
        simp [positionCoverAux, positionFold, ha]
      have atNil : positionCover lo hi (h + 1) i =
          positionCover lo hi h i.left ++ positionCover lo hi h i.right := by
        change positionCoverAux lo hi (h + 1) i [] = _
        rw [step [], ih i.left]
        rfl
      rw [step tail, ih i.left, ih i.right, atNil, List.append_assoc]

/-- Querying a disjoint node emits nothing. -/
private theorem positionCover_skip {lo hi h : Nat} {i : PositionInterval}
    (ha : positionAction lo hi i = .skip) : positionCover lo hi h i = [] := by
  cases h <;> simp [positionCover, positionCoverAux, positionFold, ha]

/-- Querying a wholly contained node emits that node, without descending. -/
private theorem positionCover_emit {lo hi h : Nat} {i : PositionInterval}
    (ha : positionAction lo hi i = .emit) : positionCover lo hi h i = [i] := by
  cases h <;> simp [positionCover, positionCoverAux, positionFold, ha]

/-- The cover at a partial overlap concatenates the two child covers in position order. -/
private theorem positionCover_split {lo hi h : Nat} {i : PositionInterval}
    (ha : positionAction lo hi i = .split) :
    positionCover lo hi (h + 1) i =
      positionCover lo hi h i.left ++ positionCover lo hi h i.right := by
  change positionCoverAux lo hi (h + 1) i [] = _
  have step : positionCoverAux lo hi (h + 1) i [] =
      positionCoverAux lo hi h i.left (positionCoverAux lo hi h i.right []) := by
    simp [positionCoverAux, positionFold, ha]
  rw [step, positionCoverAux_append]
  rfl

/-- Every emitted interval is nonempty and is contained in the starting interval and query. -/
private theorem positionCover_subinterval {lo hi h : Nat} {i j : PositionInterval}
    (hj : j ∈ positionCover lo hi h i) :
    0 < j.len ∧ i.start ≤ j.start ∧ j.stop ≤ i.stop ∧ lo ≤ j.start ∧ j.stop ≤ hi := by
  induction h generalizing i with
  | zero =>
    cases ha : positionAction lo hi i with
    | skip => simp [positionCover_skip ha] at hj
    | emit =>
      simp only [positionCover_emit ha, List.mem_singleton] at hj
      subst j
      exact ⟨(positionAction_emit ha).1, le_rfl, le_rfl, (positionAction_emit ha).2⟩
    | split => simp [positionCover, positionCoverAux, positionFold, ha] at hj
  | succ h ih =>
    cases ha : positionAction lo hi i with
    | skip => simp [positionCover_skip ha] at hj
    | emit =>
      simp only [positionCover_emit ha, List.mem_singleton] at hj
      subst j
      exact ⟨(positionAction_emit ha).1, le_rfl, le_rfl, (positionAction_emit ha).2⟩
    | split =>
      rw [positionCover_split ha, List.mem_append] at hj
      rcases hj with hj | hj
      · have hl := ih hj
        simp only [PositionInterval.left, PositionInterval.stop] at hl ⊢
        omega
      · have hr := ih hj
        simp only [PositionInterval.right, PositionInterval.stop] at hr ⊢
        omega

/-- Exact coverage: a position is in some emitted interval iff it belongs to the intersection. -/
theorem positionCover_contains_iff {lo hi h p : Nat} {i : PositionInterval}
    (hf : i.len ≤ 2 ^ h) :
    (∃ j ∈ positionCover lo hi h i, j.Contains p) ↔ i.Contains p ∧ lo ≤ p ∧ p < hi := by
  constructor
  · rintro ⟨j, hj, hp⟩
    have hs := positionCover_subinterval hj
    unfold PositionInterval.Contains at hp ⊢
    omega
  · intro ⟨hp, hq⟩
    induction h generalizing i with
    | zero =>
      cases ha : positionAction lo hi i with
      | skip => exact (positionAction_skip ha hp hq).elim
      | emit => exact ⟨i, by simp [positionCover_emit ha], hp⟩
      | split =>
        have hn := (positionAction_split ha).1
        simp at hf
        omega
    | succ h ih =>
      cases ha : positionAction lo hi i with
      | skip => exact (positionAction_skip ha hp hq).elim
      | emit => exact ⟨i, by simp [positionCover_emit ha], hp⟩
      | split =>
        have hb := PositionInterval.child_fuel hf
        rw [positionCover_split ha]
        rcases (i.contains_children p).mp hp with hp | hp
        · obtain ⟨j, hj, hjp⟩ := ih hb.1 hp
          exact ⟨j, List.mem_append_left _ hj, hjp⟩
        · obtain ⟨j, hj, hjp⟩ := ih hb.2 hp
          exact ⟨j, List.mem_append_right _ hj, hjp⟩

/-- Distinct list positions of the cover are ordered and do not overlap. -/
theorem positionCover_pairwise (lo hi h : Nat) (i : PositionInterval) :
    (positionCover lo hi h i).Pairwise (fun j k => j.stop ≤ k.start) := by
  induction h generalizing i with
  | zero =>
    cases ha : positionAction lo hi i <;>
      simp [positionCover, positionCoverAux, positionFold, ha]
  | succ h ih =>
    cases ha : positionAction lo hi i with
    | skip => simp [positionCover_skip ha]
    | emit => simp [positionCover_emit ha]
    | split =>
      rw [positionCover_split ha, List.pairwise_append]
      refine ⟨ih i.left, ih i.right, ?_⟩
      intro j hj k hk
      have hl := (positionCover_subinterval hj).2.2.1
      have hr := (positionCover_subinterval hk).2.1
      exact hl.trans hr

/-- One unit for a query endpoint strictly inside the node, zero otherwise. -/
private def positionEndpointCharge (i : PositionInterval) (p : Nat) : Nat :=
  if i.start < p ∧ p < i.stop then 1 else 0

/-- An endpoint is in at most one child interior. At the split boundary it is in neither. -/
private theorem positionEndpointCharge_children (i : PositionInterval) (p : Nat) :
    positionEndpointCharge i.left p + positionEndpointCharge i.right p ≤
      positionEndpointCharge i p := by
  unfold positionEndpointCharge
  by_cases hl : i.left.start < p ∧ p < i.left.stop
  · have hr : ¬ (i.right.start < p ∧ p < i.right.stop) := by
      simp only [PositionInterval.left, PositionInterval.right, PositionInterval.stop] at hl ⊢
      omega
    have hp : i.start < p ∧ p < i.stop := by
      simp only [PositionInterval.left, PositionInterval.stop] at hl ⊢
      omega
    rw [ite_eq_left hl, ite_eq_right hr, ite_eq_left hp]
  · rw [ite_eq_right hl]
    by_cases hr : i.right.start < p ∧ p < i.right.stop
    · have hp : i.start < p ∧ p < i.stop := by
        simp only [PositionInterval.right, PositionInterval.stop] at hr ⊢
        omega
      rw [ite_eq_left hr, ite_eq_left hp]
    · rw [ite_eq_right hr]
      exact Nat.zero_le _

/-- Number of query endpoints strictly inside a node (between zero and two). -/
private def positionEndpointBudget (lo hi : Nat) (i : PositionInterval) : Nat :=
  positionEndpointCharge i lo + positionEndpointCharge i hi

private theorem positionEndpointBudget_le (lo hi : Nat) (i : PositionInterval) :
    positionEndpointBudget lo hi i ≤ 2 := by
  unfold positionEndpointBudget positionEndpointCharge
  split <;> split <;> omega

private theorem positionEndpointBudget_split {lo hi : Nat} {i : PositionInterval}
    (ha : positionAction lo hi i = .split) : 1 ≤ positionEndpointBudget lo hi i := by
  have he := (positionAction_split ha).2
  unfold positionEndpointBudget positionEndpointCharge
  split <;> split <;> omega

/-- Endpoint-sensitive visit bound for the actual fold. No size assumption is needed: reducing
fuel can only stop an otherwise valid split earlier. -/
private theorem positionVisits_le_endpointBudget (lo hi h : Nat) (i : PositionInterval) :
    positionVisits lo hi h i ≤ 1 + (2 * h) * positionEndpointBudget lo hi i := by
  induction h generalizing i with
  | zero =>
    cases ha : positionAction lo hi i <;> simp [positionVisits, positionFold, ha]
  | succ h ih =>
    cases ha : positionAction lo hi i with
    | skip => simp [positionVisits, positionFold, ha]
    | emit => simp [positionVisits, positionFold, ha]
    | split =>
      have step : positionVisits lo hi (h + 1) i =
          1 + positionVisits lo hi h i.left + positionVisits lo hi h i.right := by
        simp [positionVisits, positionFold, ha]
      rw [step, Nat.mul_succ, Nat.add_mul]
      have hlo := positionEndpointCharge_children i lo
      have hhi := positionEndpointCharge_children i hi
      have hb : positionEndpointBudget lo hi i.left + positionEndpointBudget lo hi i.right ≤
          positionEndpointBudget lo hi i := by
        unfold positionEndpointBudget
        omega
      have hmul := Nat.mul_le_mul_left (2 * h) hb
      rw [Nat.mul_add] at hmul
      have hpos := positionEndpointBudget_split ha
      have hl := ih i.left
      have hr := ih i.right
      omega

/-- The shared traversal visits at most `1 + 4 * h` nodes. -/
theorem positionVisits_le (lo hi h : Nat) (i : PositionInterval) :
    positionVisits lo hi h i ≤ 1 + 4 * h := by
  have hb := Nat.mul_le_mul_left (2 * h) (positionEndpointBudget_le lo hi i)
  have hv := positionVisits_le_endpointBudget lo hi h i
  omega

/-- At most one interval is emitted per visit. -/
private theorem positionCover_length_le_visits (lo hi h : Nat) (i : PositionInterval) :
    (positionCover lo hi h i).length ≤ positionVisits lo hi h i := by
  induction h generalizing i with
  | zero => cases ha : positionAction lo hi i <;>
      simp [positionCover, positionCoverAux, positionVisits, positionFold, ha]
  | succ h ih =>
    cases ha : positionAction lo hi i with
    | skip => simp [positionCover_skip ha, positionVisits, positionFold, ha]
    | emit => simp [positionCover_emit ha, positionVisits, positionFold, ha]
    | split =>
      have step : positionVisits lo hi (h + 1) i =
          1 + positionVisits lo hi h i.left + positionVisits lo hi h i.right := by
        simp [positionVisits, positionFold, ha]
      rw [positionCover_split ha, List.length_append, step]
      have hl := ih i.left
      have hr := ih i.right
      omega

/-- The number of emitted canonical nodes is at most `1 + 4 * h`. -/
theorem positionCover_length_le (lo hi h : Nat) (i : PositionInterval) :
    (positionCover lo hi h i).length ≤ 1 + 4 * h :=
  (positionCover_length_le_visits lo hi h i).trans (positionVisits_le lo hi h i)

/-- A Boolean cutoff is true before false, in catalog order. -/
def CatalogCutoffPrefix (q : β → Bool) (xs : List β) : Prop :=
  xs.Pairwise (fun x y => q y = true → q x = true)

/-- The rank of a cutoff counts the items for which it is true. -/
def catalogRank (q : β → Bool) (xs : List β) : Nat :=
  (xs.filter q).length

private theorem catalog_filter_eq_nil_of_head_false {q : β → Bool} {x : β} {xs : List β}
    (h : CatalogCutoffPrefix q (x :: xs)) (hx : ¬ q x = true) :
    (x :: xs).filter q = [] := by
  apply List.filter_eq_nil_iff.mpr
  intro y hy hqy
  rcases List.mem_cons.mp hy with rfl | hy
  · exact hx hqy
  · exact hx ((List.pairwise_cons.mp h).1 y hy hqy)

/-- At each valid index of a monotone catalog, the predicate is true exactly below its rank. -/
private theorem catalogCutoffPrefix_getElem_iff {q : β → Bool} {xs : List β}
    (h : CatalogCutoffPrefix q xs) (i : Nat) (hi : i < xs.length) :
    q xs[i] = true ↔ i < catalogRank q xs := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons x xs ih =>
    by_cases hx : q x = true
    · rw [catalogRank, List.filter_cons_of_pos hx, List.length_cons]
      cases i with
      | zero => simp [hx]
      | succ i =>
        simpa [catalogRank] using ih (List.pairwise_cons.mp h).2 i (by simpa using hi)
    · rw [catalogRank, catalog_filter_eq_nil_of_head_false h hx]
      simp only [List.length_nil, Nat.not_lt_zero, iff_false]
      intro hqi
      exact (List.filter_eq_nil_iff.mp (catalog_filter_eq_nil_of_head_false h hx)) _
        (List.getElem_mem hi) hqi

/-- Search the item interval `[lo, hi)`, returning the cutoff and the number of midpoint reads.
The fuel is chosen by `catalogCutoff`; exhausted fuel does not perform a probe. -/
private def catalogCutoffGo (a : Array β) (q : β → Bool) :
    (fuel lo hi : Nat) → hi ≤ a.size → Nat × Nat
  | 0, lo, _, _ => (lo, 0)
  | fuel + 1, lo, hi, hb =>
    if h : lo < hi then
      let m := lo + (hi - lo) / 2
      have hm : m < hi := by dsimp [m]; omega
      let r := if q (a[m]'(Nat.lt_of_lt_of_le hm hb)) then
        catalogCutoffGo a q fuel (m + 1) hi hb
      else
        catalogCutoffGo a q fuel lo m (Nat.le_trans (Nat.le_of_lt hm) hb)
      (r.1, r.2 + 1)
    else (lo, 0)

private theorem catalogCutoffGo_spec (a : Array β) (q : β → Bool) (rank : Nat)
    (hq : ∀ i (hi : i < a.size), q a[i] = true ↔ i < rank)
    (fuel lo hi : Nat) (hb : hi ≤ a.size) (hl : lo ≤ rank) (hr : rank ≤ hi)
    (hw : hi - lo < 2 ^ fuel) :
    (catalogCutoffGo a q fuel lo hi hb).1 = rank ∧
      (catalogCutoffGo a q fuel lo hi hb).2 ≤ fuel := by
  induction fuel generalizing lo hi with
  | zero =>
    simp only [Nat.pow_zero] at hw
    exact ⟨by simp [catalogCutoffGo]; omega, by simp [catalogCutoffGo]⟩
  | succ fuel ih =>
    by_cases h : lo < hi
    · let m := lo + (hi - lo) / 2
      have hm : m < hi := by dsimp [m]; omega
      have hb' : m < a.size := Nat.lt_of_lt_of_le hm hb
      have hmlo : lo ≤ m := by dsimp [m]; omega
      rw [Nat.pow_succ] at hw
      have hwLeft : m - lo < 2 ^ fuel := by dsimp [m]; omega
      have hwRight : hi - (m + 1) < 2 ^ fuel := by dsimp [m]; omega
      by_cases hq' : q a[m] = true
      · have hl' : m + 1 ≤ rank := (hq m hb').mp hq'
        obtain ⟨hpos, hcost⟩ := ih (m + 1) hi hb hl' hr hwRight
        simp only [catalogCutoffGo, dite_eq_left h, ← show m = lo + (hi - lo) / 2 from rfl,
          ite_eq_left hq', hpos, true_and]
        exact Nat.succ_le_succ hcost
      · have hr' : rank ≤ m := Nat.le_of_not_gt (fun hlt => hq' ((hq m hb').mpr hlt))
        obtain ⟨hpos, hcost⟩ := ih lo m (by omega) hl hr' hwLeft
        simp only [catalogCutoffGo, dite_eq_left h, ← show m = lo + (hi - lo) / 2 from rfl,
          ite_eq_right hq', hpos, true_and]
        exact Nat.succ_le_succ hcost
    · simp only [catalogCutoffGo, dite_eq_right h]
      omega

/-- Binary search a true-then-false cutoff in an existing array. The result is
`(rank, midpoint probes)`; each charged step reads exactly one array item and tests `q` once. -/
def catalogCutoff (a : Array β) (q : β → Bool) : Nat × Nat :=
  catalogCutoffGo a q (a.size.log2 + 1) 0 a.size (Nat.le_refl _)

/-- The array search returns the rank in its list view and takes at most `1 + log₂ n` probes.
The empty catalog actually takes zero probes. -/
theorem catalogCutoff_spec (a : Array β) (q : β → Bool)
    (h : CatalogCutoffPrefix q a.toList) :
    (catalogCutoff a q).1 = catalogRank q a.toList ∧
      (catalogCutoff a q).2 ≤ a.size.log2 + 1 := by
  apply catalogCutoffGo_spec
  · intro i hi
    rw [← Array.getElem_toList (show i < a.toList.length by simpa using hi)]
    exact catalogCutoffPrefix_getElem_iff h i (by simpa using hi)
  · exact Nat.zero_le _
  · simpa [catalogRank] using List.length_filter_le q a.toList
  · rw [Nat.sub_zero]
    by_cases hz : a.size = 0
    · simp [hz]
    · exact (Nat.log2_lt hz).mp (Nat.lt_succ_self _)

/-- A balanced catalog of size at most `2^h` uses at most `h+1` probes. -/
private theorem catalogCutoff_probes_le (a : Array β) (q : β → Bool) (h : Nat)
    (hn : a.size ≤ 2 ^ h) : (catalogCutoff a q).2 ≤ h + 1 := by
  have hlog : a.size.log2 ≤ h := by
    by_cases hz : a.size = 0
    · simp [hz]
    · apply Nat.le_of_lt_succ
      apply (Nat.log2_lt hz).mpr
      rw [Nat.pow_succ]
      have hp : 0 < 2 ^ h := Nat.two_pow_pos h
      omega
  have hgo (fuel lo hi : Nat) (hb : hi ≤ a.size) : (catalogCutoffGo a q fuel lo hi hb).2 ≤ fuel := by
    induction fuel generalizing lo hi with
    | zero => simp [catalogCutoffGo]
    | succ fuel ih =>
      by_cases hh : lo < hi
      · simp only [catalogCutoffGo, dite_eq_left hh]
        split <;> exact Nat.succ_le_succ (ih _ _ _)
      · simp [catalogCutoffGo, hh]
  exact (hgo _ _ _ _).trans (Nat.succ_le_succ hlog)

/-- The rank splits the catalog into the true prefix and the false suffix. -/
private theorem catalogRank_split {q : β → Bool} {xs : List β} (h : CatalogCutoffPrefix q xs) :
    xs.take (catalogRank q xs) = xs.filter q ∧
      xs.drop (catalogRank q xs) = xs.filter (fun x => !q x) := by
  induction xs with
  | nil => simp [catalogRank]
  | cons x xs ih =>
    by_cases hx : q x = true
    · obtain ⟨ht, hd⟩ := ih (List.pairwise_cons.mp h).2
      constructor
      · simpa [catalogRank, hx] using congrArg (List.cons x) ht
      · simpa [catalogRank, hx] using hd
    · rw [catalogRank, catalog_filter_eq_nil_of_head_false h hx]
      refine ⟨rfl, (List.filter_eq_self.mpr ?_).symm⟩
      intro y hy
      have hny := List.filter_eq_nil_iff.mp (catalog_filter_eq_nil_of_head_false h hx) y hy
      cases hqy : q y <;> simp_all

/-- Two monotone cutoffs delimit a slice. This also works when their ranks are inverted:
`Nat` subtraction makes the slice empty, just as the filter is then empty. -/
private theorem catalogSlice_eq_filter {xs : List β} {p q : β → Bool}
    (hp : CatalogCutoffPrefix p xs) (hq : CatalogCutoffPrefix q xs) :
    (xs.drop (catalogRank p xs)).take (catalogRank q xs - catalogRank p xs) =
      xs.filter (fun x => !p x && q x) := by
  let l := catalogRank p xs
  let u := catalogRank q xs
  let ys := xs.take u
  change (xs.drop l).take (u - l) = _
  have hprefix : (ys.take l).filter (fun x => !p x) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro x hx
    have htake : ys.take l = (xs.take l).take u := by
      simp [ys, List.take_take, Nat.min_comm]
    rw [htake] at hx
    have hmem := (List.take_sublist u (xs.take l)).subset hx
    rw [(catalogRank_split hp).1] at hmem
    simp [(List.mem_filter.mp hmem).2]
  have hsuffix : (ys.drop l).filter (fun x => !p x) = ys.drop l := by
    apply List.filter_eq_self.mpr
    intro x hx
    rw [show ys.drop l = (xs.drop l).take (u - l) from List.drop_take] at hx
    have hmem := (List.take_sublist (u - l) (xs.drop l)).subset hx
    rw [(catalogRank_split hp).2] at hmem
    exact (List.mem_filter.mp hmem).2
  calc
    (xs.drop l).take (u - l) = ys.drop l := List.drop_take.symm
    _ = ys.filter (fun x => !p x) := by
      conv_rhs => rw [← List.take_append_drop l ys]
      rw [List.filter_append, hprefix, hsuffix, List.nil_append]
    _ = _ := by rw [show ys = xs.filter q from (catalogRank_split hq).1, List.filter_filter]

section Ordered

variable [LinearOrder α]

/-- The predicate for a lower endpoint; equal keys do not count toward this rank. -/
private def catalogBelow (key : β → α) (lo : α) (x : β) : Bool := decide (key x < lo)

/-- The predicate for an inclusive upper endpoint; equal keys count toward this rank. -/
private def catalogThrough (key : β → α) (hi : α) (x : β) : Bool := decide (key x ≤ hi)

private theorem catalogBelow_prefix (key : β → α) (lo : α) {xs : List β}
    (hs : xs.Pairwise (fun x y => key x ≤ key y)) :
    CatalogCutoffPrefix (catalogBelow key lo) xs :=
  hs.imp (fun hxy hy => decide_eq_true (lt_of_le_of_lt hxy (of_decide_eq_true hy)))

private theorem catalogThrough_prefix (key : β → α) (hi : α) {xs : List β}
    (hs : xs.Pairwise (fun x y => key x ≤ key y)) :
    CatalogCutoffPrefix (catalogThrough key hi) xs :=
  hs.imp (fun hxy hy => decide_eq_true (le_trans hxy (of_decide_eq_true hy)))

/-- Lower-bound binary search, returning `(position, probes)`. -/
private def catalogLower (key : β → α) (a : Array β) (lo : α) : Nat × Nat :=
  catalogCutoff a (catalogBelow key lo)

/-- Upper-bound binary search, returning `(position, probes)`. -/
private def catalogUpper (key : β → α) (a : Array β) (hi : α) : Nat × Nat :=
  catalogCutoff a (catalogThrough key hi)

private theorem catalogLower_spec (key : β → α) (a : Array β) (lo : α)
    (hs : a.toList.Pairwise (fun x y => key x ≤ key y)) :
    (catalogLower key a lo).1 = catalogRank (catalogBelow key lo) a.toList ∧
      (catalogLower key a lo).2 ≤ a.size.log2 + 1 :=
  catalogCutoff_spec a _ (catalogBelow_prefix key lo hs)

private theorem catalogUpper_spec (key : β → α) (a : Array β) (hi : α)
    (hs : a.toList.Pairwise (fun x y => key x ≤ key y)) :
    (catalogUpper key a hi).1 = catalogRank (catalogThrough key hi) a.toList ∧
      (catalogUpper key a hi).2 ≤ a.size.log2 + 1 :=
  catalogCutoff_spec a _ (catalogThrough_prefix key hi hs)

/-- The lower/upper search positions delimit exactly the closed interval in list order.
No assumptions on the endpoints are needed, including `lo ≤ hi`. -/
private theorem catalogClosedSlice_eq_filter (key : β → α) (a : Array β) (lo hi : α)
    (hs : a.toList.Pairwise (fun x y => key x ≤ key y)) :
    (a.toList.drop (catalogLower key a lo).1).take
        ((catalogUpper key a hi).1 - (catalogLower key a lo).1) =
      a.toList.filter (fun x => decide (lo ≤ key x ∧ key x ≤ hi)) := by
  rw [(catalogLower_spec key a lo hs).1, (catalogUpper_spec key a hi hs).1,
    catalogSlice_eq_filter (catalogBelow_prefix key lo hs) (catalogThrough_prefix key hi hs)]
  apply List.filter_congr
  intro x _
  by_cases hlo : key x < lo
  · simp [catalogBelow, hlo, not_le.mpr hlo]
  · simp [catalogBelow, catalogThrough, hlo, not_lt.mp hlo]

end Ordered

/-- Given a child catalog `parent.filter p`, store its rank at every parent gap.
One prefix scan computes the counts; the resulting lookup table is an array. -/
def catalogTransfer (parent : List β) (p : β → Bool) : Array Nat :=
  (parent.scanl (fun acc x => acc + if p x then 1 else 0) 0).toArray

@[simp] theorem catalogTransfer_size (parent : List β) (p : β → Bool) :
    (catalogTransfer parent p).size = parent.length + 1 := by
  simp [catalogTransfer]

private theorem catalog_foldl_count (p : β → Bool) (xs : List β) (acc : Nat) :
    xs.foldl (fun n x => n + if p x then 1 else 0) acc = acc + catalogRank p xs := by
  induction xs generalizing acc with
  | nil => simp [catalogRank]
  | cons x xs ih =>
    rw [List.foldl_cons, ih]
    simp only [catalogRank, List.filter_cons]
    split <;> simp
    omega

/-- The actual indexed entry at any parent gap, including `parent.length`. -/
theorem catalogTransfer_getElem_gap (parent : List β) (p : β → Bool) (j : Nat)
    (hj : j < (catalogTransfer parent p).size) :
    (catalogTransfer parent p)[j] = ((parent.take j).filter p).length := by
  let counts := parent.scanl (fun acc x => acc + if p x then 1 else 0) 0
  have hj' : j < counts.toArray.size := hj
  change counts.toArray[j]'hj' = _
  rw [List.getElem_toArray hj']
  exact (List.getElem_scanl (l := parent) (a := 0)
    (f := fun acc x => acc + if p x then 1 else 0) (by simpa [counts] using hj')).trans (by
      rw [catalog_foldl_count, Nat.zero_add]; rfl)

/-- The true-prefix property survives passing to a filtered child. -/
private theorem CatalogCutoffPrefix.filter {parent : List β} {q : β → Bool}
    (h : CatalogCutoffPrefix q parent) (p : β → Bool) :
    CatalogCutoffPrefix q (parent.filter p) :=
  List.Pairwise.filter p h

/-- One array read at the parent's cutoff rank returns the corresponding child's rank. -/
theorem catalogTransfer_getElem {parent : List β} (p : β → Bool) {q : β → Bool}
    (hq : CatalogCutoffPrefix q parent) :
    (catalogTransfer parent p)[catalogRank q parent]'(by
      simpa [catalogRank, Nat.lt_succ_iff] using List.length_filter_le q parent) =
        catalogRank q (parent.filter p) := by
  rw [catalogTransfer_getElem_gap, (catalogRank_split hq).1, catalogRank,
    List.filter_filter, List.filter_filter]
  simp only [Bool.and_comm]

/-- One indexed read after the parent search supplies the child boundary; no child
search (or scan of the child) is needed. Applies to either ordered endpoint. -/
private theorem catalogTransfer_getElem_cutoff (a : Array β) (p q : β → Bool)
    (hq : CatalogCutoffPrefix q a.toList) :
    (catalogTransfer a.toList p)[(catalogCutoff a q).1]'(by
      rw [(catalogCutoff_spec a q hq).1, catalogTransfer_size]
      exact Nat.lt_succ_of_le (List.length_filter_le q a.toList)) =
        catalogRank q (a.toList.filter p) := by
  generalize_proofs
  convert catalogTransfer_getElem p hq using 2
  exact (catalogCutoff_spec a q hq).1

variable {κ : Type w}

/-- The next `n` entries of `xs` starting at position `s`. -/
private def span (xs : List β) (s n : Nat) : List β := (xs.drop s).take n

/-- The stable key order of all entries, tagged with their original positions. -/
private def taggedY [LE κ] [DecidableLE κ] (key : β → κ) (xs : List β) : List (β × Nat) :=
  xs.zipIdx.mergeSort (fun p q : β × Nat => decide (key p.1 ≤ key q.1))

/-- Whether a tag lies in the half-open interval `[s, s + n)`. -/
private def byPos (s n : Nat) (p : β × Nat) : Bool := decide (s ≤ p.2 ∧ p.2 < s + n)

/-- The key-sorted catalog for the position interval `[s, s + n)`. -/
private def ys [LE κ] [DecidableLE κ] (key : β → κ) (xs : List β) (s n : Nat) : List (β × Nat) :=
  (taggedY key xs).filter (byPos s n)

private theorem tagged_zipIdx_nodup (xs : List β) (i : Nat) : (xs.zipIdx i).Nodup := by
  have h : ((xs.zipIdx i).map Prod.snd).Nodup := by
    rw [List.zipIdx_map_snd]
    exact List.nodup_range' _
  exact (List.pairwise_map.mp h).imp fun hne heq => hne (congrArg Prod.snd heq)

private theorem tagged_filter_byPos_perm (xs : List β) (s n : Nat) :
    (xs.zipIdx.filter (byPos s n)).Perm ((span xs s n).zipIdx s) := by
  classical
  have hd : (xs.zipIdx.filter (byPos s n)).Nodup :=
    (tagged_zipIdx_nodup xs 0).filter _
  apply (List.perm_ext_iff_of_nodup hd (tagged_zipIdx_nodup _ _)).2
  intro p
  rw [List.mem_filter, List.mem_zipIdx_iff_getElem?, List.mem_zipIdx_iff_le_and_getElem?_sub]
  simp only [byPos, decide_eq_true_eq, span, List.getElem?_take]
  by_cases hs : s ≤ p.2
  · by_cases hn : p.2 - s < n
    · have hi : p.2 < s + n := by omega
      simp [hs, hn, hi, List.getElem?_drop, Nat.add_sub_of_le hs]
    · have hi : ¬ p.2 < s + n := by omega
      simp [hs, hn, hi]
  · simp [hs]

variable [LE κ] [DecidableLE κ]

/-- The catalog contains precisely the slice's tagged occurrences, starting at tag `s`. -/
private theorem ys_perm_zipIdx_span (key : β → κ) (xs : List β) (s n : Nat) :
    (ys key xs s n).Perm ((span xs s n).zipIdx s) := by
  unfold ys taggedY
  exact ((List.mergeSort_perm _ _).filter _).trans (tagged_filter_byPos_perm xs s n)

/-- Forgetting tags leaves a permutation of the original slice. -/
private theorem ys_map_fst_perm_span (key : β → κ) (xs : List β) (s n : Nat) :
    ((ys key xs s n).map Prod.fst).Perm (span xs s n) := by
  simpa only [List.zipIdx_map_fst] using (ys_perm_zipIdx_span key xs s n).map Prod.fst

/-- The catalog is nondecreasing by key. -/
private theorem ys_pairwise [Std.IsLinearPreorder κ] (key : β → κ) (xs : List β) (s n : Nat) :
    (ys key xs s n).Pairwise (fun p q => key p.1 ≤ key q.1) := by
  have h : (taggedY key xs).Pairwise (fun p q => decide (key p.1 ≤ key q.1) = true) := by
    unfold taggedY
    apply List.pairwise_mergeSort
    · intro a b c
      simp only [decide_eq_true_eq]
      exact fun hab hbc => Std.le_trans hab hbc
    · intro a b
      simpa only [Bool.or_eq_true, decide_eq_true_eq] using
        (Std.le_total (a := key a.1) (b := key b.1))
  simpa only [ys, decide_eq_true_eq] using h.filter (byPos s n)

private theorem tagged_ys_filter_of_bounds (key : β → κ) (xs : List β) {s n t m : Nat}
    (h₁ : s ≤ t) (h₂ : t + m ≤ s + n) :
    (ys key xs s n).filter (byPos t m) = ys key xs t m := by
  simp only [ys, List.filter_filter]
  apply List.filter_congr
  intro p _
  by_cases hc : t ≤ p.2 ∧ p.2 < t + m
  · have hp : s ≤ p.2 ∧ p.2 < s + n :=
      ⟨Nat.le_trans h₁ hc.1, Nat.lt_of_lt_of_le hc.2 h₂⟩
    simp [byPos, hc, hp]
  · simp [byPos, hc]

/-- Selecting the left half of the parent preserves its catalog order. -/
private theorem ys_filter_left (key : β → κ) (xs : List β) (s n : Nat) :
    (ys key xs s n).filter (byPos s (n / 2)) = ys key xs s (n / 2) := by
  apply tagged_ys_filter_of_bounds key xs (Nat.le_refl s)
  exact Nat.add_le_add_left (Nat.div_le_self n 2) s

/-- Selecting the right half of the parent preserves its catalog order. -/
private theorem ys_filter_right (key : β → κ) (xs : List β) (s n : Nat) :
    (ys key xs s n).filter (byPos (s + n / 2) (n - n / 2)) =
      ys key xs (s + n / 2) (n - n / 2) := by
  apply tagged_ys_filter_of_bounds key xs
  · omega
  · have h := Nat.div_le_self n 2
    omega

/-- An in-bounds position interval has exactly `n` catalog entries. -/
private theorem ys_length (key : β → κ) (xs : List β) (s n : Nat) (h : s + n ≤ xs.length) :
    (ys key xs s n).length = n := by
  rw [(ys_perm_zipIdx_span key xs s n).length_eq, List.length_zipIdx]
  apply List.length_take_of_le
  rw [List.length_drop]
  omega

private def sorted [LinearOrder α] (key : β → α) (xs : List β) : List β :=
  xs.mergeSort fun x y => decide (key x ≤ key y)

private theorem sorted_perm [LinearOrder α] (key : β → α) (xs : List β) :
    (sorted key xs).Perm xs := List.mergeSort_perm _ _

private theorem sorted_pairwise [LinearOrder α] (key : β → α) (xs : List β) :
    (sorted key xs).Pairwise (fun x y => key x ≤ key y) := by
  simpa [sorted] using (List.pairwise_mergeSort (le := fun x y => decide (key x ≤ key y))
    (fun a b c => by simpa using (le_trans : key a ≤ key b → key b ≤ key c → key a ≤ key c))
    (fun a b => by simpa using (le_total (key a) (key b))) xs)

private theorem span_length (xs : List β) {s n : Nat} (hn : s + n ≤ xs.length) :
    (span xs s n).length = n := by
  simp only [span, List.length_take, List.length_drop]
  omega

private theorem span_append (xs : List β) (s m n : Nat) :
    span xs s m ++ span xs (s + m) n = span xs s (m+n) := by
  simp [span, List.take_add, List.drop_drop, Nat.add_comm s m]

private theorem span_zero (xs : List β) (s : Nat) : span xs s 0 = [] := by simp [span]

private theorem span_all (xs : List β) : span xs 0 xs.length = xs := by simp [span]

private theorem span_eq_filter (xs : List β) (p : β → Bool) (a b s n : Nat)
    (h : ∀ j (hj : j < xs.length), p xs[j] = decide (a ≤ j ∧ j < b))
    (hdis : b ≤ a ∨ s+n ≤ a ∨ b ≤ s) : (span xs s n).filter p = [] := by
  rw [List.filter_eq_nil_iff]
  intro x hx
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hx
  have hj' : s+j < xs.length := by
    simp [span, List.length_take, List.length_drop] at hj
    omega
  have hjn : j < n := by simp [span, List.length_take, List.length_drop] at hj; omega
  simpa [span, List.getElem_take, List.getElem_drop, h (s+j) hj'] using
    (show ¬(a ≤ s+j ∧ s+j < b) by omega)

private theorem span_filter_full (xs : List β) (p : β → Bool) (a b s n : Nat)
    (h : ∀ j (hj : j < xs.length), p xs[j] = decide (a ≤ j ∧ j < b))
    (hin : a ≤ s ∧ s+n ≤ b) : (span xs s n).filter p = span xs s n := by
  rw [List.filter_eq_self]
  intro x hx
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hx
  have hj' : s+j < xs.length := by
    simp [span, List.length_take, List.length_drop] at hj
    omega
  have hjn : j < n := by simp [span, List.length_take, List.length_drop] at hj; omega
  simpa [span, List.getElem_take, List.getElem_drop, h (s+j) hj'] using
    (show a ≤ s+j ∧ s+j < b by omega)

section Traversal

variable {σ : Type t} {τ : Type r} {S : Type w}

private inductive Tree (σ : Type v) (τ : Type w) where
  | empty
  | leaf (payload : σ)
  | fork (payload : σ) (links : τ) (left right : Tree σ τ)

private def Tree.build (data : Nat → Nat → σ) (links : Nat → Nat → τ) :
    Nat → Nat → Nat → Tree σ τ
  | 0, s, n => if n = 0 then .empty else .leaf (data s n)
  | h+1, s, n =>
    if n = 0 then .empty
    else if n = 1 then .leaf (data s n)
    else .fork (data s n) (links s n) (build data links h s (n/2))
      (build data links h (s+n/2) (n-n/2))

private def Tree.cells (width : σ → Nat) (linkWidth : τ → Nat) : Tree σ τ → Nat
  | .empty => 0
  | .leaf x => 1 + width x
  | .fork x links l r => 1 + width x + linkWidth links + l.cells width linkWidth +
    r.cells width linkWidth

private theorem halves_le (h n : Nat) (hn : n ≤ 2^(h+1)) :
    n/2 ≤ 2^h ∧ n-n/2 ≤ 2^h := by
  rw [Nat.pow_succ] at hn
  omega

private theorem Tree.cells_build_le (data : Nat → Nat → σ) (links : Nat → Nat → τ)
    (width : σ → Nat) (linkWidth : τ → Nat) (limit scale : Nat)
    (hb : ∀ s n, s+n ≤ limit → 0 < n →
      1 + width (data s n) + linkWidth (links s n) ≤ n * scale)
    (h s n : Nat) (hn : s+n ≤ limit) :
    (Tree.build data links h s n).cells width linkWidth ≤ n * scale * (h+1) := by
  induction h generalizing s n with
  | zero =>
    by_cases hz : n = 0
    · simp [Tree.build, Tree.cells, hz]
    · have := hb s n hn (by omega)
      simp [Tree.build, Tree.cells, hz]
      omega
  | succ h ih =>
    by_cases hz : n = 0
    · simp [Tree.build, Tree.cells, hz]
    have hnode := hb s n hn (by omega)
    by_cases ho : n = 1
    · have hg : n * scale * 1 ≤ n * scale * (h+1+1) := Nat.mul_le_mul_left _ (by omega)
      simp [Tree.build, Tree.cells, ho] at hnode hg ⊢
      omega
    · simp only [Tree.build, hz, ho, ite_false, Tree.cells]
      have hl := ih s (n/2) (by omega)
      have hr := ih (s+n/2) (n-n/2) (by omega)
      have he : n/2 + (n-n/2) = n := by omega
      calc
        _ ≤ n * scale + (n/2 * scale * (h+1) + (n-n/2) * scale * (h+1)) := by omega
        _ = n * scale * (h+1+1) := by
          rw [← Nat.add_mul, ← Nat.add_mul, he, Nat.mul_add (n * scale) (h+1) 1,
            Nat.mul_one, Nat.add_comm]

-- A continuation carries one output tail and the running charge. Its proofs below are erased;
-- the only operation on an existing output tail in the executable path is to pass it to the
-- next continuation. In particular, neither composition nor finalization traverses that tail.
private abbrev Output (β : Type v) := List β × Nat

private structure Run (β : Type v) where
  emit : Output β → Output β
  search : Nat
  prepend : ∀ tail, (emit tail).1 = (emit ([], 0)).1 ++ tail.1
  counted : ∀ tail, (emit tail).2 + tail.1.length = (emit tail).1.length + tail.2

private def Run.points (r : Run β) : List β := (r.emit ([], 0)).1

private def Run.empty (search : Nat) : Run β := ⟨id, search, by simp, by simp [Nat.add_comm]⟩

-- Compose once, then invoke right once and left once on the resulting tail. This preserves
-- left-to-right output order without building either child's independent output list.
private def Run.combine (l r : Run β) : Run β where
  emit tail := l.emit (r.emit tail)
  search := l.search + r.search
  prepend tail := by rw [l.prepend (r.emit tail), r.prepend tail, l.prepend (r.emit ([], 0)), List.append_assoc]
  counted tail := by
    have hr := r.counted tail
    have hl := l.counted (r.emit tail)
    omega

private def Run.extra (r : Run β) (k : Nat) : Run β := { r with search := r.search + k }

@[simp] private theorem Run.points_empty (cost : Nat) : (Run.empty cost : Run β).points = [] := rfl

@[simp] private theorem Run.points_extra (r : Run β) (k : Nat) : (r.extra k).points = r.points := rfl

@[simp] private theorem Run.points_combine (l r : Run β) :
    (l.combine r).points = l.points ++ r.points := by
  exact l.prepend (r.emit ([], 0))

/-- The returned list, its search charge and the counted output emissions. The emitted count is
computed during reporting, not by scanning the returned list. -/
structure Result (β : Type v) where
  points : List β
  search : Nat
  emitted : Nat
  emitted_eq : emitted = points.length

/-- Search charge plus the counted emissions. On a report, this is one output charge per point. -/
def Result.work (r : Result β) : Nat := r.search + r.emitted

private def Run.finish (r : Run β) : Result β :=
  let out := r.emit ([], 0)
  ⟨out.1, r.search, out.2, by simpa using r.counted ([], 0)⟩

-- A visit charges interval tests, call/return, dispatch, and constructing and applying the
-- corresponding continuation; for a layered split it includes up to four indexed table reads.
-- Each root visit also covers query setup and termination (including its endpoint searches'
-- fixed setup/exit operations). Each terminal emit visit includes iterator setup and exit.
private def Tree.walk (emit : σ → S → Run β) (transfer : τ → S → S × S)
    (a b : Nat) : Tree σ τ → Nat → Nat → S → Run β
  | .empty, _, _, _ => Run.empty 1
  | .leaf x, s, n, st =>
    if positionAction a b ⟨s,n⟩ = .emit then (emit x st).extra 1 else Run.empty 1
  | .fork x links l r, s, n, st =>
    match positionAction a b ⟨s,n⟩ with
    | .skip => Run.empty 1
    | .emit => (emit x st).extra 1
    | .split =>
      let st' := transfer links st
      ((walk emit transfer a b l s (n/2) st'.1).combine
        (walk emit transfer a b r (s+n/2) (n-n/2) st'.2)).extra 1

private theorem Tree.walk_build_perm
    (data : Nat → Nat → σ) (links : Nat → Nat → τ)
    (emit : σ → S → Run β) (transfer : τ → S → S × S) (a b limit : Nat)
    (ok : Nat → Nat → S → Prop) (target : Nat → Nat → List β)
    (hzero : ∀ s, target s 0 = [])
    (hout : ∀ s n, s+n ≤ limit → positionAction a b ⟨s,n⟩ = .skip → target s n = [])
    (hin : ∀ s n st, s+n ≤ limit → 0 < n → ok s n st → positionAction a b ⟨s,n⟩ = .emit →
      (emit (data s n) st).points.Perm (target s n))
    (hnext : ∀ s n st, s+n ≤ limit → ok s n st →
      ok s (n/2) (transfer (links s n) st).1 ∧
      ok (s+n/2) (n-n/2) (transfer (links s n) st).2)
    (hcat : ∀ s n, target s (n/2) ++ target (s+n/2) (n-n/2) = target s n)
    (h s n : Nat) (st : S) (hn : n ≤ 2^h) (hs : s+n ≤ limit) (hst : ok s n st) :
    ((Tree.build data links h s n).walk emit transfer a b s n st).points.Perm (target s n) := by
  induction h generalizing s n st with
  | zero =>
    by_cases hz : n = 0
    · subst n; simp [Tree.build, Tree.walk, hzero]
    have ho : n = 1 := by simp at hn; omega
    have hcase (he : positionAction a b ⟨s,n⟩ = .split) : False := by
      have hp := (positionAction_split he).1
      change 2 ≤ n at hp
      omega
    cases hc : positionAction a b ⟨s,n⟩ with
    | skip => simp [Tree.build, Tree.walk, hz, hc, hout s n hs hc]
    | emit => simpa [Tree.build, Tree.walk, hz, hc] using
        (hin s n st hs (by omega) hst hc)
    | split => exact (hcase hc).elim
  | succ h ih =>
    by_cases hz : n = 0
    · subst n; simp [Tree.build, Tree.walk, hzero]
    by_cases ho : n = 1
    · subst n
      have hcase (he : positionAction a b ⟨s,1⟩ = .split) : False := by
        have hp := (positionAction_split he).1
        change 2 ≤ 1 at hp
        omega
      cases hc : positionAction a b ⟨s,1⟩ with
      | skip => simp [Tree.build, Tree.walk, hc, hout s 1 hs hc]
      | emit => simpa [Tree.build, Tree.walk, hc] using
          (hin s 1 st hs (by omega) hst hc)
      | split => exact (hcase hc).elim
    · cases hc : positionAction a b ⟨s,n⟩ with
      | skip => simp [Tree.build, Tree.walk, hz, ho, hc, hout s n hs hc]
      | emit => simpa [Tree.build, Tree.walk, hz, ho, hc] using
          (hin s n st hs (by omega) hst hc)
      | split =>
        obtain ⟨hl, hr⟩ := halves_le h n hn
        obtain ⟨sl, sr⟩ := hnext s n st hs hst
        have pl := ih s (n/2) _ hl (by omega) sl
        have pr := ih (s+n/2) (n-n/2) _ hr (by omega) sr
        rw [← hcat s n]
        simp only [Tree.build, hz, ho, ite_false, Tree.walk, hc, Run.points_extra, Run.points_combine]
        exact pl.append pr

end Traversal

section SearchCharge

variable {σ : Type t} {τ : Type r} {S : Type w}

private theorem Tree.walk_build_search_le
    (data : Nat → Nat → σ) (links : Nat → Nat → τ)
    (emit : σ → S → Run β) (transfer : τ → S → S × S) (a b limit budget : Nat)
    (hemit : ∀ s n st, s+n ≤ limit → 0 < n → (emit (data s n) st).search ≤ budget)
    (h s n : Nat) (st : S) (hn : n ≤ 2^h) (hs : s+n ≤ limit) :
    ((Tree.build data links h s n).walk emit transfer a b s n st).search ≤
      positionVisits a b h ⟨s,n⟩ * (budget+1) := by
  induction h generalizing s n st with
  | zero =>
    by_cases hz : n = 0
    · simp [Tree.build, Tree.walk, hz, Run.empty, positionVisits_zero]
    have hp := hemit s n st hs (by omega)
    by_cases hc : positionAction a b ⟨s,n⟩ = .emit <;>
      simp [Tree.build, Tree.walk, hz, hc, positionVisits_zero, Run.empty, Run.extra]
    exact hp
  | succ h ih =>
    by_cases hz : n = 0
    · subst n
      have hc : positionAction a b ⟨s,0⟩ = .skip := by simp [positionAction]
      simp [Tree.build, Tree.walk, Run.empty, positionVisits_skip hc]
    have hp := hemit s n st hs (by omega)
    by_cases ho : n = 1
    · subst n
      cases hc : positionAction a b ⟨s,1⟩ with
      | skip => simp [Tree.build, Tree.walk, hc, Run.empty, positionVisits_skip hc]
      | emit => simp [Tree.build, Tree.walk, hc, positionVisits_emit hc, Run.extra]; omega
      | split =>
        have he := (positionAction_split hc).1
        change 2 ≤ 1 at he
        omega
    · cases hc : positionAction a b ⟨s,n⟩ with
      | skip => simp [Tree.build, Tree.walk, hz, ho, hc, Run.empty, positionVisits_skip hc]
      | emit => simp [Tree.build, Tree.walk, hz, ho, hc, positionVisits_emit hc, Run.extra]; omega
      | split =>
        obtain ⟨hl, hr⟩ := halves_le h n hn
        have pl := ih s (n/2) (transfer (links s n) st).1 hl (by omega)
        have pr := ih (s+n/2) (n-n/2) (transfer (links s n) st).2 hr (by omega)
        rw [positionVisits_split hc, Nat.add_mul, Nat.add_mul]
        simp [Tree.build, Tree.walk, hz, ho, hc, Run.extra, Run.combine,
          PositionInterval.left, PositionInterval.right] at pl pr ⊢
        omega

end SearchCharge

section Nesting

variable {δ : Type w} [LinearOrder α]

private def closed (key : β → α) (q : α × α) (p : β) : Bool :=
  decide (q.1 ≤ key p ∧ key p ≤ q.2)

private def boxMatch (key : Nat → β → α) (base : β → Bool) :
    Nat → List (α × α) → β → Bool
  | _, [], p => base p
  | j, q :: qs, p => closed (key j) q p && boxMatch key base (j+1) qs p

private def bounds (key : β → α) (a : Array β) (q : α × α) : (Nat × Nat) × Nat :=
  let l := catalogLower key a q.1
  let r := catalogUpper key a q.2
  ((l.1, r.1), l.2 + r.2)

private theorem bounds_probes_le (key : β → α) (a : Array β) (q : α × α)
    {h : Nat} (hn : a.size ≤ 2^h) : (bounds key a q).2 ≤ 2*(h+1) := by
  have hl := catalogCutoff_probes_le a (catalogBelow key q.1) h hn
  have hu := catalogCutoff_probes_le a (catalogThrough key q.2) h hn
  change (catalogLower key a q.1).2 ≤ _ at hl
  change (catalogUpper key a q.2).2 ≤ _ at hu
  dsimp [bounds]
  omega

private theorem closed_eq_position (key : β → α) (q : α × α) (xs : List β)
    (hs : xs.Pairwise (fun x y => key x ≤ key y)) (i : Nat) (hi : i < xs.length) :
    closed key q xs[i] =
      decide ((bounds key xs.toArray q).1.1 ≤ i ∧ i < (bounds key xs.toArray q).1.2) := by
  have hs' : xs.toArray.toList.Pairwise (fun x y => key x ≤ key y) := by simpa using hs
  have hl := (catalogLower_spec key xs.toArray q.1 hs').1
  have hu := (catalogUpper_spec key xs.toArray q.2 hs').1
  simp at hl hu
  have hl2 := catalogCutoffPrefix_getElem_iff (catalogBelow_prefix key q.1 hs) i hi
  have hu2 := catalogCutoffPrefix_getElem_iff (catalogThrough_prefix key q.2 hs) i hi
  simp only [catalogBelow, catalogThrough, decide_eq_true_eq] at hl2 hu2
  simp only [bounds, hl, hu, closed, decide_eq_decide]
  rw [← Nat.not_lt, ← hl2, ← hu2, not_lt]

private theorem span_filter_skip (xs : List β) (p : β → Bool) (a b s n : Nat)
    (hp : ∀ j (hj : j < xs.length), p xs[j] = decide (a ≤ j ∧ j < b))
    (hc : positionAction a b ⟨s,n⟩ = .skip) : (span xs s n).filter p = [] := by
  by_cases hn : n = 0
  · simp [hn, span]
  apply span_eq_filter _ _ _ _ _ _ hp
  unfold positionAction PositionInterval.stop at hc
  split at hc
  · rename_i h
    simp only at h
    omega
  · split at hc <;> contradiction

private inductive Nested (β : Type v) (δ : Type w) where
  | base (data : δ)
  | more (catalog : Array β) (tree : Tree (Nested β δ) Unit)

private def Nested.build (base : List β → δ) (key : Nat → β → α) (h : Nat) :
    Nat → Nat → List β → Nested β δ
  | 0, _, xs => .base (base xs)
  | d+1, j, xs =>
    let xs' := sorted (key j) xs
    .more xs'.toArray (Tree.build (fun s n => build base key h d (j+1) (span xs' s n))
      (fun _ _ => ()) h 0 xs'.length)

private def Nested.query (base : δ → Run β) (key : Nat → β → α) :
    List (α × α) → Nat → Nested β δ → Run β
  | [], _, .base data => base data
  | q :: qs, j, .more arr tree =>
    let r := bounds (key j) arr q
    (tree.walk (fun x (_ : Unit) => query base key qs (j+1) x) (fun _ _ => ((), ()))
      r.1.1 r.1.2 0 arr.size ()).extra r.2
  | _, _, _ => Run.empty 0

private def Nested.cells (base : δ → Nat) : Nat → Nested β δ → Nat
  | 0, .base data => base data
  | d+1, .more arr tree => arr.size + tree.cells (cells base d) (fun _ => 0)
  | _, _ => 0

private theorem Nested.query_perm (baseBuild : List β → δ) (baseQuery : δ → Run β)
    (key : Nat → β → α) (p : β → Bool)
    (h : Nat) (hbase : ∀ xs, xs.length ≤ 2^h → (baseQuery (baseBuild xs)).points.Perm (xs.filter p)) (qs : List (α × α)) (j : Nat) (xs : List β) (hn : xs.length ≤ 2^h) :
    (query baseQuery key qs j (build baseBuild key h qs.length j xs)).points.Perm
      (xs.filter (boxMatch key p j qs)) := by
  induction qs generalizing j xs with
  | nil => exact hbase xs hn
  | cons q qs ih =>
    let ys := sorted (key j) xs
    have hys := sorted_perm (key j) xs
    have hl : ys.length = xs.length := hys.length_eq
    let r := bounds (key j) ys.toArray q
    let tail := boxMatch key p (j+1) qs
    have hp := closed_eq_position (key j) q ys (sorted_pairwise (key j) xs)
    let target := fun s n => ((span ys s n).filter (closed (key j) q)).filter tail
    have hb : ∀ s n, s+n ≤ ys.length → 0 < n → True →
        positionAction r.1.1 r.1.2 ⟨s,n⟩ = .emit →
        (query baseQuery key qs (j+1) (build baseBuild key h qs.length (j+1)
          (span ys s n))).points.Perm (target s n) := by
      intro s n hs _ _ hc
      have hh := (positionAction_emit hc).2
      change r.1.1 ≤ s ∧ s+n ≤ r.1.2 at hh
      have ih' := ih (j+1) (span ys s n) (by rw [span_length _ hs]; omega)
      simpa only [target, span_filter_full _ _ _ _ _ _ hp hh] using ih'
    have hc : ∀ s n, s+n ≤ ys.length → positionAction r.1.1 r.1.2 ⟨s,n⟩ = .skip →
        target s n = [] := by
      intro s n _ hs
      change ((span ys s n).filter (closed (key j) q)).filter tail = []
      rw [span_filter_skip _ _ _ _ _ _ hp hs]
      rfl
    have hcat (s n : Nat) : target s (n/2) ++ target (s+n/2) (n-n/2) = target s n := by
      have he : n/2 + (n-n/2) = n := by omega
      simp only [target, ← List.filter_append, span_append, he]
    have exec := Tree.walk_build_perm
      (fun s n => build baseBuild key h qs.length (j+1) (span ys s n)) (fun _ _ => ())
      (fun x (_ : Unit) => query baseQuery key qs (j+1) x) (fun _ _ => ((), ())) r.1.1 r.1.2
      ys.length (fun _ _ _ => True) target (by simp [target, span]) hc (fun s n _ => hb s n)
      (by simp) hcat h 0 ys.length () (by simpa [hl] using hn) (by simp) trivial
    have hexec : (query baseQuery key (q::qs) j
        (build baseBuild key h (q::qs).length j xs)).points.Perm (target 0 ys.length) := by
      change ((Tree.build _ _ h 0 ys.length).walk _ _ r.1.1 r.1.2 0 ys.toArray.size ()).points.Perm _
      simpa using exec
    apply hexec.trans
    simpa [target, boxMatch, span_all, List.filter_filter, tail, Bool.and_comm] using
      hys.filter (boxMatch key p j (q::qs))

-- The same scale absorbs the fixed-size charges of either kind of final catalog.
private def scale (h : Nat) : Nat := 10*(h+1)

private theorem scale_pow_pos (h d : Nat) : 0 < scale h ^ d := by
  apply Nat.pow_pos
  simp [scale]

private theorem Nested.query_search_le (baseBuild : List β → δ) (baseQuery : δ → Run β)
    (key : Nat → β → α) (h power : Nat)
    (hbase : ∀ xs, xs.length ≤ 2^h → (baseQuery (baseBuild xs)).search ≤ scale h ^ power)
    (qs : List (α × α)) (j : Nat) (xs : List β) (hn : xs.length ≤ 2^h) :
    (query baseQuery key qs j (build baseBuild key h qs.length j xs)).search ≤
      scale h ^ (power + qs.length) := by
  induction qs generalizing j xs with
  | nil => simpa only [List.length_nil, Nat.add_zero, Nested.query, Nested.build] using hbase xs hn
  | cons q qs ih =>
    let ys := sorted (key j) xs
    have hl : ys.length = xs.length := (sorted_perm (key j) xs).length_eq
    let r := bounds (key j) ys.toArray q
    let k := scale h ^ (power + qs.length)
    have hb (s n : Nat) (hs : s+n ≤ ys.length) :
        (query baseQuery key qs (j+1) (build baseBuild key h qs.length (j+1)
          (span ys s n))).search ≤ k :=
      ih (j+1) _ (by rw [span_length _ hs]; omega)
    have hv := Tree.walk_build_search_le
      (fun s n => build baseBuild key h qs.length (j+1) (span ys s n)) (fun _ _ => ())
      (fun x (_ : Unit) => query baseQuery key qs (j+1) x) (fun _ _ => ((), ())) r.1.1 r.1.2
      ys.length k (fun s n _ hs _ => hb s n hs) h 0 ys.length () (by simpa [hl] using hn) (by simp)
    have hp : r.2 ≤ 2*(h+1) := bounds_probes_le _ _ _ (by simpa [hl] using hn)
    have hvisit : positionVisits r.1.1 r.1.2 h ⟨0,ys.length⟩ ≤ 4*(h+1) := by
      have := positionVisits_le r.1.1 r.1.2 h ⟨0,ys.length⟩
      omega
    have hcharge := hv.trans (Nat.mul_le_mul_right (k+1) hvisit)
    change ((Tree.build _ _ h 0 ys.length).walk _ _ r.1.1 r.1.2 0 ys.toArray.size ()).search +
      r.2 ≤ scale h ^ (power + (q::qs).length)
    simp only [List.length_cons, ← Nat.add_assoc power qs.length 1, Nat.pow_succ]
    rw [Nat.mul_comm _ (scale h)]
    change _ ≤ scale h * k
    rw [show ys.toArray.size = ys.length by simp]
    have hk : 1 ≤ k := scale_pow_pos _ _
    have hh := Nat.mul_le_mul_left (h+1) hk
    simp only [Nat.mul_one] at hh
    refine (Nat.add_le_add hcharge hp).trans ?_
    rw [scale, Nat.mul_assoc, Nat.mul_add, Nat.mul_one, Nat.mul_assoc]
    omega

private theorem Nested.cells_le (baseBuild : List β → δ) (baseCells : δ → Nat)
    (key : Nat → β → α) (h power factor : Nat) (hf : 0 < factor)
    (hbase : ∀ xs, xs.length ≤ 2^h → baseCells (baseBuild xs) ≤ xs.length * (factor * scale h ^ power))
    (d j : Nat) (xs : List β) (hn : xs.length ≤ 2^h) :
    cells baseCells d (build baseBuild key h d j xs) ≤ xs.length * (factor * scale h ^ (power + d)) := by
  induction d generalizing j xs with
  | zero => exact hbase xs hn
  | succ d ih =>
    let ys := sorted (key j) xs
    have hl : ys.length = xs.length := (sorted_perm (key j) xs).length_eq
    let k := factor * scale h ^ (power + d)
    have hk (s n : Nat) (hs : s+n ≤ ys.length) :
        cells baseCells d (build baseBuild key h d (j+1) (span ys s n)) ≤ n * k := by
      have ht := ih (j+1) (span ys s n) (by rw [span_length _ hs]; omega)
      rwa [span_length _ hs] at ht
    have hp := Tree.cells_build_le
      (fun s n => build baseBuild key h d (j+1) (span ys s n)) (fun _ _ => ())
      (cells baseCells d) (fun _ => 0) ys.length (k+1)
      (fun s n hs hn => by have := hk s n hs; rw [Nat.mul_add, Nat.mul_one]; omega)
      h 0 ys.length (by simp)
    change ys.toArray.size + (Tree.build _ _ h 0 ys.length).cells _ _ ≤ _
    rw [show ys.toArray.size = ys.length by simp, ← hl]
    rw [← Nat.add_assoc power d 1, Nat.pow_succ, ← Nat.mul_assoc factor]
    change ys.length + _ ≤ ys.length * (k * scale h)
    apply (Nat.add_le_add_left hp _).trans
    have hkl : 1 ≤ k := Nat.mul_pos hf (scale_pow_pos _ _)
    have hc (m : Nat) : m + m * (k+1) * (h+1) ≤ m * (k * scale h) := by
      calc
        _ = m * (1 + (k+1)*(h+1)) := by
          rw [Nat.mul_add m 1, Nat.mul_one, Nat.mul_assoc m (k+1)]
        _ ≤ _ := by
          apply Nat.mul_le_mul_left
          have ha := Nat.mul_le_mul_right (h+1) hkl
          simp only [Nat.one_mul] at ha
          rw [scale, Nat.add_mul k 1 (h+1), Nat.one_mul, ← Nat.mul_assoc k 10 (h+1),
            Nat.mul_comm k 10, Nat.mul_assoc 10 k (h+1)]
          omega
    exact hc _

end Nesting

section BaseCatalogs

variable [LinearOrder α]

variable {γ : Type t}

-- Descending indices let us prepend the slice in array order, without copying the tail.
private def emitSliceLoop (a : Array γ) (project : γ → β) (lo hi : Nat)
    (hhi : hi ≤ a.size) (tail : List β) : List β :=
  if h : lo < hi then
    emitSliceLoop a project lo (hi - 1) (by omega)
      (project (getElem a (hi - 1) (by omega)) :: tail)
  else tail
termination_by hi
decreasing_by omega

private def emitSlice (a : Array γ) (project : γ → β) (ends : Nat × Nat)
    (tail : List β) : List β :=
  emitSliceLoop a project ends.1 (min ends.2 a.size) (Nat.min_le_right ..) tail

private def sliceCount (a : Array γ) (ends : Nat × Nat) : Nat :=
  min ends.2 a.size - ends.1

private theorem emitSliceLoop_eq (a : Array γ) (project : γ → β) (lo hi : Nat)
    (hhi : hi ≤ a.size) (tail : List β) :
    emitSliceLoop a project lo hi hhi tail =
      ((a.toList.drop lo).take (hi - lo)).map project ++ tail := by
  rw [emitSliceLoop]
  split
  next h =>
    rw [emitSliceLoop_eq]
    have hidx : hi - 1 - lo < (a.toList.drop lo).length := by
      simp only [List.length_drop, Array.length_toList]
      omega
    have hsize : hi - lo = hi - 1 - lo + 1 := by omega
    have hshift : lo + (hi - 1 - lo) = hi - 1 := by omega
    rw [hsize, List.take_succ_eq_append_getElem hidx, List.getElem_drop, Array.getElem_toList]
    simp [hshift, List.append_assoc]
  next h =>
    have hzero : hi - lo = 0 := by omega
    simp [hzero]
termination_by hi
decreasing_by omega

private theorem emitSlice_eq (a : Array γ) (project : γ → β) (ends : Nat × Nat)
    (tail : List β) :
    emitSlice a project ends tail =
      ((a.toList.drop ends.1).take (ends.2 - ends.1)).map project ++ tail := by
  rw [emitSlice, emitSliceLoop_eq]
  by_cases h : ends.2 ≤ a.size
  · rw [Nat.min_eq_left h]
  · rw [Nat.min_eq_right (by omega), List.take_of_length_le, List.take_of_length_le]
    all_goals simp only [List.length_drop, Array.length_toList]; omega

-- Proof-only execution trace: each `step` records one indexed read and one cons.
-- There is no counter in the executable loop.
private inductive EmitSliceRun (a : Array γ) (project : γ → β) (lo : Nat) :
    Nat → List β → List β → Nat → Prop where
  | stop {hi tail} (h : hi ≤ lo) : EmitSliceRun a project lo hi tail tail 0
  | step {hi tail out steps} (h : lo < hi) (hhi : hi ≤ a.size)
      (next : EmitSliceRun a project lo (hi - 1)
        (project (getElem a (hi - 1) (by omega)) :: tail) out steps) :
      EmitSliceRun a project lo hi tail out (steps + 1)

private theorem emitSliceLoop_work (a : Array γ) (project : γ → β) (lo hi : Nat)
    (hhi : hi ≤ a.size) (tail : List β) :
    EmitSliceRun a project lo hi tail (emitSliceLoop a project lo hi hhi tail) (hi - lo) := by
  rw [emitSliceLoop]
  split
  next h =>
    have hsteps : hi - lo = hi - 1 - lo + 1 := by omega
    rw [hsteps]
    exact .step h hhi (emitSliceLoop_work a project lo (hi - 1) (by omega) _)
  next h =>
    have hstop : hi ≤ lo := by omega
    simpa only [Nat.sub_eq_zero_of_le hstop] using
      (EmitSliceRun.stop (a := a) (project := project) (tail := tail) hstop)
termination_by hi
decreasing_by omega

private theorem emitSlice_work (a : Array γ) (project : γ → β) (ends : Nat × Nat)
    (tail : List β) :
    EmitSliceRun a project ends.1 (min ends.2 a.size) tail
      (emitSlice a project ends tail) (sliceCount a ends) :=
  emitSliceLoop_work a project ends.1 (min ends.2 a.size) (Nat.min_le_right ..) tail


private theorem EmitSliceRun.length_eq {a : Array γ} {project : γ → β}
    {lo hi : Nat} {tail out : List β} {steps : Nat}
    (trace : EmitSliceRun a project lo hi tail out steps) : out.length = steps + tail.length := by
  induction trace with
  | stop => simp
  | step _ _ _ ih =>
      simp only [List.length_cons] at ih
      omega

private theorem emitSlice_length (a : Array γ) (project : γ → β) (ends : Nat × Nat)
    (tail : List β) : (emitSlice a project ends tail).length = sliceCount a ends + tail.length :=
  (emitSlice_work a project ends tail).length_eq

private def runSlice {γ : Type t} (a : Array γ) (project : γ → β) (ends : Nat × Nat) : Run β where
  emit tail := (emitSlice a project ends tail.1, tail.2 + sliceCount a ends)
  search := 0
  prepend tail := by simp only [emitSlice_eq, List.append_nil]
  counted tail := by
    simp only [emitSlice_length]
    omega

private theorem runSlice_points {γ : Type t} (a : Array γ) (project : γ → β) (ends : Nat × Nat) :
    (runSlice a project ends).points =
      ((a.toList.drop ends.1).take (ends.2 - ends.1)).map project := by
  simp [Run.points, runSlice, emitSlice_eq]

-- The one-coordinate case keeps one shared ordered catalog and a balanced leaf tree.
-- Full nodes emit a slice of the shared catalog instead of storing a second copy of it.
private abbrev Line (β : Type v) := Array β × Tree (Nat × Nat) Unit

private def lineBuild (h : Nat) (key : β → α) (xs : List β) : Line β :=
  let ys := sorted key xs
  (ys.toArray, Tree.build Prod.mk (fun _ _ => ()) h 0 ys.length)

private def lineEmit (a : Array β) (span : Nat × Nat) (_ : Unit) : Run β :=
  runSlice a id (span.1, span.1 + span.2)

private def lineQuery (key : β → α) (q : α × α) (i : Line β) : Run β :=
  let r := bounds key i.1 q
  (i.2.walk (lineEmit i.1) (fun _ _ => ((), ())) r.1.1 r.1.2 0 i.1.size ()).extra r.2

private def lineCells (i : Line β) : Nat := i.1.size + i.2.cells (fun _ => 0) (fun _ => 0)

private theorem line_perm (h : Nat) (key : β → α) (q : α × α) (xs : List β)
    (hn : xs.length ≤ 2^h) :
    (lineQuery key q (lineBuild h key xs)).points.Perm (xs.filter (closed key q)) := by
  let yz := sorted key xs
  have hl : yz.length = xs.length := (sorted_perm key xs).length_eq
  let r := bounds key yz.toArray q
  have hp := closed_eq_position key q yz (sorted_pairwise key xs)
  let target := fun s n => (span yz s n).filter (closed key q)
  have hout : ∀ s n, s+n ≤ yz.length → positionAction r.1.1 r.1.2 ⟨s,n⟩ = .skip →
      target s n = [] := by
    intro s n _ ha
    exact span_filter_skip _ _ _ _ _ _ hp ha
  have hin : ∀ s n (st : Unit), s+n ≤ yz.length → 0 < n → True →
      positionAction r.1.1 r.1.2 ⟨s,n⟩ = .emit →
      (lineEmit yz.toArray (s,n) st).points.Perm (target s n) := by
    intro s n st _ _ _ ha
    have hh := (positionAction_emit ha).2
    change r.1.1 ≤ s ∧ s+n ≤ r.1.2 at hh
    change (runSlice yz.toArray id (s,s+n)).points.Perm ((span yz s n).filter (closed key q))
    rw [runSlice_points, span_filter_full _ _ _ _ _ _ hp hh]
    simp [span]
  have hcat (s n : Nat) : target s (n/2) ++ target (s+n/2) (n-n/2) = target s n := by
    have he : n/2 + (n-n/2) = n := by omega
    simp only [target, ← List.filter_append, span_append, he]
  have ht := Tree.walk_build_perm Prod.mk (fun _ _ => ()) (lineEmit yz.toArray) (fun _ _ => ((), ()))
    r.1.1 r.1.2 yz.length (fun _ _ _ => True) target (by simp [target, span]) hout hin (by simp)
    hcat h 0 yz.length () (by simpa [hl] using hn) (by simp) True.intro
  have hq : (lineQuery key q (lineBuild h key xs)).points.Perm (target 0 yz.length) := by
    change ((Tree.build Prod.mk (fun _ _ => ()) h 0 yz.length).walk (lineEmit yz.toArray)
      (fun _ _ => ((), ())) r.1.1 r.1.2 0 yz.toArray.size ()).points.Perm _
    simpa using ht
  apply hq.trans
  simpa [target, span_all] using (sorted_perm key xs).filter (closed key q)

private theorem line_search_le (h : Nat) (key : β → α) (q : α × α) (xs : List β)
    (hn : xs.length ≤ 2^h) : (lineQuery key q (lineBuild h key xs)).search ≤ scale h := by
  let yz := sorted key xs
  have hyz : yz.length ≤ 2^h := by simpa [yz, (sorted_perm key xs).length_eq] using hn
  let r := bounds key yz.toArray q
  have hp : r.2 ≤ 2*(h+1) := bounds_probes_le _ _ _ (by simpa using hyz)
  have hw := Tree.walk_build_search_le Prod.mk (fun _ _ => ()) (lineEmit yz.toArray)
    (fun _ _ => ((), ())) r.1.1 r.1.2 yz.length 0 (by intros; rfl)
    h 0 yz.length () hyz (by simp)
  have hm := positionVisits_le r.1.1 r.1.2 h ⟨0,yz.length⟩
  change ((Tree.build Prod.mk (fun _ _ => ()) h 0 yz.length).walk (lineEmit yz.toArray)
    (fun _ _ => ((), ())) r.1.1 r.1.2 0 yz.toArray.size ()).search + r.2 ≤ scale h
  rw [show yz.toArray.size = yz.length by simp]
  simp only [Nat.zero_add, Nat.mul_one] at hw
  unfold scale
  omega

private theorem line_tree_cells_le (h s n : Nat) :
    (Tree.build Prod.mk (fun _ _ => ()) h s n).cells (fun _ => 0) (fun _ => 0) ≤ 2*n-1 := by
  induction h generalizing s n with
  | zero =>
    by_cases hn : n = 0
    · simp [Tree.build, Tree.cells, hn]
    · simp [Tree.build, Tree.cells, hn]; omega
  | succ h ih =>
    by_cases hn : n = 0
    · simp [Tree.build, Tree.cells, hn]
    by_cases ho : n = 1
    · simp [Tree.build, Tree.cells, ho]
    have hl := ih s (n/2)
    have hr := ih (s+n/2) (n-n/2)
    simp [Tree.build, Tree.cells, hn, ho]
    omega

private theorem line_cells_le (h : Nat) (key : β → α) (xs : List β) :
    lineCells (lineBuild h key xs) ≤ xs.length * 3 := by
  let yz := sorted key xs
  have hl : yz.length = xs.length := (sorted_perm key xs).length_eq
  have ht := line_tree_cells_le h 0 yz.length
  change yz.toArray.size + (Tree.build Prod.mk (fun _ _ => ()) h 0 yz.length).cells _ _ ≤ _
  rw [show yz.toArray.size = yz.length by simp]
  omega

private abbrev Plane (β : Type v) := Array β × Array (β × Nat) ×
  Tree (Array (β × Nat)) (Array Nat × Array Nat)

private def leftLinks (zs : List (β × Nat)) (s n : Nat) : Array Nat :=
  catalogTransfer zs (byPos s (n/2))

private def rightLinks (zs : List (β × Nat)) (s n : Nat) : Array Nat :=
  catalogTransfer zs (byPos (s+n/2) (n-n/2))

private def planeBuild (h : Nat) (kx ky : β → α) (xs : List β) : Plane β :=
  let xs' := sorted kx xs
  let c := ys ky xs'
  (xs'.toArray, (c 0 xs'.length).toArray,
    Tree.build (fun s n => (c s n).toArray)
      (fun s n => (leftLinks (c s n) s n, rightLinks (c s n) s n)) h 0 xs'.length)

private def follow (l : Array Nat) (r : Nat × Nat) : Nat × Nat :=
  (l[r.1]?.getD 0, l[r.2]?.getD 0)

private def followBoth (links : Array Nat × Array Nat) (r : Nat × Nat) :
    (Nat × Nat) × (Nat × Nat) := (follow links.1 r, follow links.2 r)

private def planeEmit (a : Array (β × Nat)) (r : Nat × Nat) : Run β :=
  runSlice a Prod.fst r

private def planeQuery (kx ky : β → α) (qx qy : α × α) (index : Plane β) : Run β :=
  let rx := bounds kx index.1 qx
  let ry := bounds (fun z => ky z.1) index.2.1 qy
  (index.2.2.walk planeEmit followBoth rx.1.1 rx.1.2 0 index.1.size ry.1).extra (rx.2+ry.2)

private def planeCells (index : Plane β) : Nat :=
  index.1.size + index.2.1.size + index.2.2.cells Array.size (fun c => c.1.size + c.2.size)

private def lastRanks (ky : β → α) (qy : α × α) (zs : List (β × Nat)) : Nat × Nat :=
  (catalogRank (catalogBelow (fun p => ky p.1) qy.1) zs,
    catalogRank (catalogThrough (fun p => ky p.1) qy.2) zs)

private theorem follow_rank (zs : List (β × Nat)) (p q : (β × Nat) → Bool)
    (hq : CatalogCutoffPrefix q zs) :
    (catalogTransfer zs p)[catalogRank q zs]?.getD 0 = catalogRank q (zs.filter p) := by
  have hh : catalogRank q zs < (catalogTransfer zs p).size := by
    simpa [catalogRank, Nat.lt_succ_iff] using List.length_filter_le q zs
  rw [Array.getElem?_eq_getElem hh]
  simp only [Option.getD_some]
  exact catalogTransfer_getElem p hq

private theorem follow_last (ky : β → α) (qy : α × α) (zs : List (β × Nat))
    (hs : zs.Pairwise (fun x y => ky x.1 ≤ ky y.1)) (p : (β × Nat) → Bool) :
    follow (catalogTransfer zs p) (lastRanks ky qy zs) = lastRanks ky qy (zs.filter p) := by
  apply Prod.ext
  · exact follow_rank zs p _ (catalogBelow_prefix (fun x : β × Nat => ky x.1) qy.1 hs)
  · exact follow_rank zs p _ (catalogThrough_prefix (fun x : β × Nat => ky x.1) qy.2 hs)

private theorem bounds_eq_last (ky : β → α) (qy : α × α) (zs : List (β × Nat))
    (hs : zs.Pairwise (fun x y => ky x.1 ≤ ky y.1)) :
    (bounds (fun x : β × Nat => ky x.1) zs.toArray qy).1 = lastRanks ky qy zs := by
  have hs' : zs.toArray.toList.Pairwise (fun x y => ky x.1 ≤ ky y.1) := by simpa using hs
  apply Prod.ext
  · simpa [bounds, lastRanks] using (catalogLower_spec (fun x : β × Nat => ky x.1) zs.toArray qy.1 hs').1
  · simpa [bounds, lastRanks] using (catalogUpper_spec (fun x : β × Nat => ky x.1) zs.toArray qy.2 hs').1

private theorem plane_emit_perm (ky : β → α) (qy : α × α) (zs : List (β × Nat))
    (hs : zs.Pairwise (fun x y => ky x.1 ≤ ky y.1)) :
    (planeEmit zs.toArray (lastRanks ky qy zs)).points = (zs.map Prod.fst).filter (closed ky qy) := by
  rw [← bounds_eq_last ky qy zs hs]
  have hs' : zs.toArray.toList.Pairwise (fun x y => ky x.1 ≤ ky y.1) := by simpa using hs
  change (runSlice zs.toArray Prod.fst (bounds (fun x : β × Nat => ky x.1) zs.toArray qy).1).points = _
  rw [runSlice_points]
  change (((zs.toArray.toList.drop (catalogLower (fun x : β × Nat => ky x.1) zs.toArray qy.1).1).take
    ((catalogUpper (fun x : β × Nat => ky x.1) zs.toArray qy.2).1 -
    (catalogLower (fun x : β × Nat => ky x.1) zs.toArray qy.1).1))).map Prod.fst = _
  rw [catalogClosedSlice_eq_filter _ _ _ _ hs', List.filter_map]
  rfl

private theorem plane_perm (h : Nat) (kx ky : β → α) (qx qy : α × α) (xs : List β)
    (hn : xs.length ≤ 2^h) :
    (planeQuery kx ky qx qy (planeBuild h kx ky xs)).points.Perm
      (xs.filter (fun p => closed kx qx p && closed ky qy p)) := by
  let xx := sorted kx xs
  have hxx := sorted_perm kx xs
  have hl : xx.length = xs.length := hxx.length_eq
  let rx := bounds kx xx.toArray qx
  have hp := closed_eq_position kx qx xx (sorted_pairwise kx xs)
  let cat := ys ky xx
  let data := fun s n => (cat s n).toArray
  let links := fun s n => (leftLinks (cat s n) s n, rightLinks (cat s n) s n)
  let ok := fun s n r => r = lastRanks ky qy (cat s n)
  let target := fun s n => ((span xx s n).filter (closed kx qx)).filter (closed ky qy)
  have hout : ∀ s n, s+n ≤ xx.length → positionAction rx.1.1 rx.1.2 ⟨s,n⟩ = .skip →
      target s n = [] := by
    intro s n _ hh
    change ((span xx s n).filter (closed kx qx)).filter (closed ky qy) = []
    rw [span_filter_skip _ _ _ _ _ _ hp hh]
    rfl
  have hin : ∀ s n st, s+n ≤ xx.length → 0 < n → ok s n st →
      positionAction rx.1.1 rx.1.2 ⟨s,n⟩ = .emit →
      (planeEmit (data s n) st).points.Perm (target s n) := by
    intro s n st _ _ hs hc
    have hh := (positionAction_emit hc).2
    change rx.1.1 ≤ s ∧ s+n ≤ rx.1.2 at hh
    change st = lastRanks ky qy (cat s n) at hs
    change (planeEmit (cat s n).toArray st).points.Perm
      (((span xx s n).filter (closed kx qx)).filter (closed ky qy))
    rw [hs, plane_emit_perm ky qy _ (ys_pairwise ky xx s n), span_filter_full _ _ _ _ _ _ hp hh]
    exact (ys_map_fst_perm_span ky xx s n).filter _
  have hnext : ∀ s n st, s+n ≤ xx.length → ok s n st →
      ok s (n/2) (followBoth (links s n) st).1 ∧
      ok (s+n/2) (n-n/2) (followBoth (links s n) st).2 := by
    intro s n st _ hs
    change st = lastRanks ky qy (cat s n) at hs
    constructor
    · change follow (catalogTransfer (cat s n) (byPos s (n/2))) st = lastRanks ky qy (cat s (n/2))
      rw [hs, follow_last ky qy _ (ys_pairwise ky xx s n), ys_filter_left]
    · change follow (catalogTransfer (cat s n) (byPos (s+n/2) (n-n/2))) st =
        lastRanks ky qy (cat (s+n/2) (n-n/2))
      rw [hs, follow_last ky qy _ (ys_pairwise ky xx s n), ys_filter_right]
  have hcat (s n : Nat) : target s (n/2) ++ target (s+n/2) (n-n/2) = target s n := by
    have he : n/2 + (n-n/2) = n := by omega
    simp only [target, ← List.filter_append, span_append, he]
  have hst : ok 0 xx.length (bounds (fun x : β × Nat => ky x.1) (data 0 xx.length) qy).1 :=
    bounds_eq_last ky qy _ (ys_pairwise ky xx 0 xx.length)
  have ht := Tree.walk_build_perm data links planeEmit followBoth rx.1.1 rx.1.2 xx.length ok target
    (by simp [target, span]) hout hin hnext hcat h 0 xx.length _ (by simpa [hl] using hn) (by simp) hst
  have hq : (planeQuery kx ky qx qy (planeBuild h kx ky xs)).points.Perm (target 0 xx.length) := by
    change ((Tree.build data links h 0 xx.length).walk planeEmit followBoth rx.1.1 rx.1.2 0
      xx.toArray.size (bounds (fun x : β × Nat => ky x.1) (data 0 xx.length) qy).1).points.Perm _
    simpa using ht
  apply hq.trans
  simpa [target, span_all, List.filter_filter, Bool.and_comm] using
    hxx.filter (fun p => closed kx qx p && closed ky qy p)

private theorem plane_search_le (h : Nat) (kx ky : β → α) (qx qy : α × α) (xs : List β)
    (hn : xs.length ≤ 2^h) :
    (planeQuery kx ky qx qy (planeBuild h kx ky xs)).search ≤ scale h := by
  let xx := sorted kx xs
  have hl : xx.length = xs.length := (sorted_perm kx xs).length_eq
  have hxx : xx.length ≤ 2^h := hl ▸ hn
  let data := fun s n => (ys ky xx s n).toArray
  let links := fun s n => (leftLinks (ys ky xx s n) s n, rightLinks (ys ky xx s n) s n)
  let rx := bounds kx xx.toArray qx
  let ry := bounds (fun x : β × Nat => ky x.1) (data 0 xx.length) qy
  have hx : rx.2 ≤ 2*(h+1) := bounds_probes_le _ _ _ (by simpa using hxx)
  have hy : ry.2 ≤ 2*(h+1) := bounds_probes_le _ _ _ (by
    change (ys ky xx 0 xx.length).toArray.size ≤ _
    simpa [ys_length ky xx 0 xx.length (by simp)] using hxx)
  have hv := Tree.walk_build_search_le data links planeEmit followBoth rx.1.1 rx.1.2 xx.length 0
    (by intros; rfl) h 0 xx.length ry.1 hxx (by simp)
  have hm := positionVisits_le rx.1.1 rx.1.2 h (⟨0,xx.length⟩ : PositionInterval)
  change ((Tree.build data links h 0 xx.length).walk planeEmit followBoth rx.1.1 rx.1.2 0
    xx.toArray.size ry.1).search + (rx.2+ry.2) ≤ scale h
  rw [show xx.toArray.size = xx.length by simp]
  simp only [Nat.zero_add, Nat.mul_one] at hv
  unfold scale
  omega

private theorem plane_cells_le (h : Nat) (kx ky : β → α) (xs : List β) :
    planeCells (planeBuild h kx ky xs) ≤ xs.length * scale h := by
  let xx := sorted kx xs
  have hl : xx.length = xs.length := (sorted_perm kx xs).length_eq
  let data := fun s n => (ys ky xx s n).toArray
  let links := fun s n => (leftLinks (ys ky xx s n) s n, rightLinks (ys ky xx s n) s n)
  have hl' (s n : Nat) (hn : s+n ≤ xx.length) : (data s n).size = n := by
    simp [data, ys_length ky xx s n hn]
  have hx := Tree.cells_build_le data links Array.size (fun c => c.1.size + c.2.size) xx.length 6
    (fun s n hn hp => by simp [links, leftLinks, rightLinks, hl' s n hn, ys_length ky xx s n hn]; omega)
    h 0 xx.length (by simp)
  change xx.toArray.size + (data 0 xx.length).size + (Tree.build data links h 0 xx.length).cells _ _ ≤ _
  rw [show xx.toArray.size = xx.length by simp, hl' 0 _ (by simp), ← hl]
  refine (Nat.add_le_add_left hx _).trans ?_
  let m := xx.length
  change m + m + m * 6 * (h+1) ≤ m * (10*(h+1))
  calc
    _ = m * (1 + 1 + 6*(h+1)) := by
      rw [Nat.mul_add m (1+1), Nat.mul_add m 1 1, Nat.mul_one, Nat.mul_assoc m 6]
    _ ≤ _ := Nat.mul_le_mul_left _ (by omega)

end BaseCatalogs

section Reporting

variable [LinearOrder α]

/-- A point is in a box if every listed interval contains the corresponding coordinate,
starting with coordinate zero. Both ends are included and a reversed interval is empty. -/
def inBox (key : Nat → β → α) (box : List (α × α)) (p : β) : Bool :=
  boxMatch key (fun _ => true) 0 box p

private theorem boxMatch_append (key : Nat → β → α) (q : List (α × α))
    (base : β → Bool) (j : Nat) (front : List (α × α)) (p : β) :
    boxMatch key base j (front ++ q) p =
      boxMatch key (boxMatch key base (j + front.length) q) j front p := by
  induction front generalizing j with
  | nil => simp [boxMatch]
  | cons b bs ih => simp [boxMatch, ih, Nat.add_comm, Nat.add_left_comm]

private def heightBudget (n : Nat) : Nat :=
  if n ≤ 1 then 0 else (n-1).log2 + 1

private theorem heightBudget_eq_clog (n : Nat) : heightBudget n = Nat.clog 2 n := by
  by_cases h : n ≤ 1
  · simp [heightBudget, h, Nat.clog_of_right_le_one h 2]
  have hn : n-1 ≠ 0 := by omega
  rw [heightBudget, ite_eq_right h]
  apply Nat.le_antisymm
  · apply Nat.succ_le_of_lt
    apply (Nat.lt_clog_iff_pow_lt (by decide)).2
    by_contra hn'
    have hc := (Nat.log2_lt hn).2 (show n-1 < 2^(n-1).log2 by omega)
    omega
  · apply (Nat.clog_le_iff_le_pow (by decide)).2
    have hh := (Nat.log2_lt hn).1 (Nat.lt_succ_self (n-1).log2)
    omega

/-- The scale `10 (1 + ⌈log₂ n⌉)` used to give common finite bounds, with height zero at
sizes zero and one. -/
def reportingScale (n : Nat) : Nat := scale (heightBudget n)

/-- Prepared ordinary index in `d + 1` coordinates: `d` balanced nested levels followed by
one sorted catalog. An input list represents its occurrences, not a deduplicated set. -/
structure OrdinaryIndex (α : Type u) (β : Type v) (d : Nat) where
  private mk ::
  private key : Nat → β → α
  private nested : Nested β (Line β)

/-- Prepare an ordinary index, sorting by the current coordinate at each level. No preprocessing
time bound is asserted. -/
def OrdinaryIndex.build (key : Nat → β → α) (d : Nat) (xs : List β) : OrdinaryIndex α β d :=
  ⟨key, Nested.build (lineBuild (heightBudget xs.length) (key d)) key (heightBudget xs.length) d 0 xs⟩

/-- Count the occupied catalog slots and tree records of the prepared ordinary index. A slot
holds a point reference; the coordinates of the input points are not copied into every slot. -/
def OrdinaryIndex.cells {d : Nat} (idx : OrdinaryIndex α β d) : Nat :=
  idx.nested.cells lineCells d

/-- Search the front intervals in the current-coordinate catalogs and emit the last-coordinate
slices into one output tail using direct indexed reads. The length proof fixes the number of outer
levels, not the order of the query endpoints. -/
def OrdinaryIndex.report {d : Nat} (idx : OrdinaryIndex α β d) (qs : List (α × α))
    (last : α × α) (_ : qs.length = d) : Result β :=
  (idx.nested.query (lineQuery (idx.key d) last) idx.key qs 0).finish

/-- Prepared layered index in `d + 2` coordinates: `d` balanced nested levels, followed
by a two-dimensional range tree with last-coordinate catalogs and child position tables. -/
structure LayeredIndex (α : Type u) (β : Type v) (d : Nat) where
  private mk ::
  private key : Nat → β → α
  private nested : Nested β (Plane β)

/-- Prepare a layered index. At the final pair of coordinates, tag occurrences by their position
in penultimate-coordinate order and keep the parent order among tied final keys. No preprocessing
time bound is asserted. -/
def LayeredIndex.build (key : Nat → β → α) (d : Nat) (xs : List β) : LayeredIndex α β d :=
  ⟨key, Nested.build (planeBuild (heightBudget xs.length) (key d) (key (d+1)))
    key (heightBudget xs.length) d 0 xs⟩

/-- Count occupied catalog slots, position-table entries and tree records of the prepared
layered index. A tagged slot holds one point reference and one position. -/
def LayeredIndex.cells {d : Nat} (idx : LayeredIndex α β d) : Nat :=
  idx.nested.cells planeCells d

/-- Report from a prepared layered index. At each final two-coordinate subtree, search the root
last-coordinate catalog once for each boundary, follow precomputed child positions, and emit the
reported slices into one output tail using direct indexed reads. -/
def LayeredIndex.report {d : Nat} (idx : LayeredIndex α β d) (qs : List (α × α))
    (penultimate last : α × α) (_ : qs.length = d) : Result β :=
  (idx.nested.query (planeQuery (idx.key d) (idx.key (d+1)) penultimate last) idx.key qs 0).finish

/-- Ordinary orthogonal range reporting. In dimension `qs.length + 1`, the reported sequence is a
permutation of exactly the input occurrences in the closed box. With `n` inputs, `k` outputs
and `B = reportingScale n`, occupied storage is at most `n * (3 * B ^ qs.length)` and work at most
`B ^ (qs.length + 1) + k`. This includes an empty front (one dimension), an empty input, and a
singleton input. The charge counts probes, visits of the balanced position tree, and one indexed
read and cons per output occurrence in the reporting traversal, not preprocessing or evaluator time. -/
theorem ordinaryRangeReporting (key : Nat → β → α) (xs : List β) (qs : List (α × α))
    (last : α × α) :
    let i := OrdinaryIndex.build key qs.length xs
    let r := i.report qs last rfl
    r.points.Perm (xs.filter (inBox key (qs ++ [last]))) ∧
      i.cells ≤ xs.length * (3 * reportingScale xs.length ^ qs.length) ∧
      r.work ≤ reportingScale xs.length ^ (qs.length+1) + r.points.length := by
  let h := heightBudget xs.length
  have hn : xs.length ≤ 2^h := by
    dsimp [h]
    rw [heightBudget_eq_clog]
    exact Nat.le_pow_clog (by decide) _
  let k := key qs.length
  let b := lineBuild h k
  have hp := Nested.query_perm b (lineQuery k last) key (closed k last) h (line_perm h k last) qs 0 xs hn
  have hc := Nested.cells_le b lineCells key h 0 3 (by decide) (by
    intro ys _; simpa only [Nat.pow_zero, Nat.mul_one] using line_cells_le h k ys) qs.length 0 xs hn
  have hw := Nested.query_search_le b (lineQuery k last) key h 1 (by
    intro ys hy; simpa only [Nat.pow_one] using line_search_le h k last ys hy) qs 0 xs hn
  dsimp only [OrdinaryIndex.build, OrdinaryIndex.cells, OrdinaryIndex.report, Result.work, reportingScale]
  refine ⟨?_, by simpa only [Nat.zero_add] using hc, ?_⟩
  · have hb : inBox key (qs ++ [last]) = boxMatch key (closed k last) 0 qs := by
      funext x
      unfold inBox
      rw [boxMatch_append]
      simp [boxMatch, k]
    rw [hb]
    exact hp
  · rw [Result.emitted_eq]
    apply Nat.add_le_add_right
    simpa only [Run.finish, Nat.add_comm 1 qs.length] using hw

/-- Layered orthogonal range reporting. In dimension `qs.length + 2`, the reported sequence is a
permutation of exactly the input occurrences in the closed box. With `n` inputs, `k` outputs
and `B = reportingScale n`, occupied storage is at most `n * B ^ (qs.length + 1)` and work at most
`B ^ (qs.length + 1) + k`. The final-level transfer uses child-table reads at both ranks,
and the output iterator performs one indexed read and cons per occurrence. No bounded-time
transfer hypothesis, child re-search, or concatenation of intermediate output lists is needed. -/
theorem layeredRangeReporting (key : Nat → β → α) (xs : List β) (qs : List (α × α))
    (penultimate last : α × α) :
    let i := LayeredIndex.build key qs.length xs
    let r := i.report qs penultimate last rfl
    r.points.Perm (xs.filter (inBox key (qs ++ [penultimate, last]))) ∧
      i.cells ≤ xs.length * reportingScale xs.length ^ (qs.length+1) ∧
      r.work ≤ reportingScale xs.length ^ (qs.length+1) + r.points.length := by
  let h := heightBudget xs.length
  have hn : xs.length ≤ 2^h := by
    dsimp [h]
    rw [heightBudget_eq_clog]
    exact Nat.le_pow_clog (by decide) _
  let kx := key qs.length
  let ky := key (qs.length+1)
  let b := planeBuild h kx ky
  let q := planeQuery kx ky penultimate last
  have hc := Nested.cells_le b planeCells key h 1 1 (by decide) (by
    intro ys _; simpa only [Nat.pow_one, Nat.one_mul] using plane_cells_le h kx ky ys) qs.length 0 xs hn
  have hw := Nested.query_search_le b q key h 1 (by
    intro ys hy; simpa only [Nat.pow_one] using plane_search_le h kx ky penultimate last ys hy) qs 0 xs hn
  -- The generic traversal needs correctness only for subcatalogs of at most the root size.
  have hp := Nested.query_perm b q key (fun x => closed kx penultimate x && closed ky last x)
    h (fun ys hy => plane_perm h kx ky penultimate last ys hy) qs 0 xs hn
  dsimp only [LayeredIndex.build, LayeredIndex.cells, LayeredIndex.report, Result.work, reportingScale]
  refine ⟨?_, by simpa only [Nat.one_mul, Nat.add_comm 1 qs.length] using hc, ?_⟩
  · have hb : inBox key (qs ++ [penultimate, last]) =
        boxMatch key (fun x => closed kx penultimate x && closed ky last x) 0 qs := by
      funext x
      unfold inBox
      rw [boxMatch_append]
      simp [boxMatch, kx, ky]
    rw [hb]
    exact hp
  · rw [Result.emitted_eq]
    apply Nat.add_le_add_right
    simpa only [Run.finish, Nat.add_comm 1 qs.length] using hw

/-- The one-dimensional specialization uses at most `3 * n` occupied slots and tree records, and at most
`10 (1 + ⌈log₂ n⌉) + k` charged work, and reports exactly the occurrences in the closed interval. -/
theorem oneDimensionalRangeReporting (key : β → α) (xs : List β) (interval : α × α) :
    let i := OrdinaryIndex.build (fun _ => key) 0 xs
    let r := i.report [] interval rfl
    r.points.Perm (xs.filter (fun p => decide (interval.1 ≤ key p ∧ key p ≤ interval.2))) ∧
      i.cells ≤ xs.length * 3 ∧ r.work ≤ reportingScale xs.length + r.points.length := by
  have hh : inBox (fun _ => key) [interval] =
      (fun p => decide (interval.1 ≤ key p ∧ key p ≤ interval.2)) := by
    funext x
    simp [inBox, boxMatch, closed]
  simpa only [hh, List.length_nil, Nat.pow_zero, Nat.mul_one, Nat.zero_add, Nat.pow_one,
    List.nil_append] using ordinaryRangeReporting (fun _ => key) xs [] interval

end Reporting

end Cslib.Algorithms.Lean.RangeTree.OrthogonalReporting
