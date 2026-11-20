/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Assembly.MergeTreeCost
import Code.Transcription.Powerloop
import Mathlib.Tactic

/-!
# Checked replay of the interleaved PowerSort policy trace

The access trace records formed-run pushes and logical, pre-trimming merges in
one chronological channel.  This module gives that raw channel a deliberately
strict, pure semantics.  A formed-run observation is accepted only when its
post-push depth, source interval, adaptive-minrun branch, and remaining-input
metadata agree.  A merge is accepted only when its index and full source
spans identify an adjacent pair in the current forest.

Every replayed internal node is labelled by the transcribed `powerloop`
applied to the aggregate spans being merged.  No label supplied by the trace
is trusted, and physical trimming does not alter the logical merge cost.
-/

namespace CPythonListsort

/-! ## Raw event projections -/

namespace PolicyEvent

/-- The source spans of formed runs, in chronological order. -/
def formedSpans : List PolicyEvent → List RunSpan
  | [] => []
  | .formed push :: events => push.run :: formedSpans events
  | .merge _ :: events => formedSpans events

/-- The lengths of formed runs, in chronological order. -/
def formedLengths (events : List PolicyEvent) : List Nat :=
  (formedSpans events).map RunSpan.len

/-- Paper merge cost accumulated by the logical pre-trimming merge events. -/
def logicalMergeCost : List PolicyEvent → Nat
  | [] => 0
  | .formed _ :: events => logicalMergeCost events
  | .merge event :: events =>
      event.left.len + event.right.len + logicalMergeCost events

/-- The individual pre-trimming merge costs, in chronological event order.

This projection is deliberately separate from `logicalMergeCost`: executable
regressions can pin a concrete merge schedule rather than only its total. -/
def logicalMergeCosts : List PolicyEvent → List Nat
  | [] => []
  | .formed _ :: events => logicalMergeCosts events
  | .merge event :: events =>
      (event.left.len + event.right.len) :: logicalMergeCosts events

@[simp]
theorem formedSpans_nil : formedSpans [] = [] := rfl

@[simp]
theorem formedSpans_formed (push : PendingPushEvent)
    (events : List PolicyEvent) :
    formedSpans (.formed push :: events) = push.run :: formedSpans events := rfl

@[simp]
theorem formedSpans_merge (event : LogicalMergeEvent)
    (events : List PolicyEvent) :
    formedSpans (.merge event :: events) = formedSpans events := rfl

@[simp]
theorem formedLengths_nil : formedLengths [] = [] := rfl

@[simp]
theorem formedLengths_formed (push : PendingPushEvent)
    (events : List PolicyEvent) :
    formedLengths (.formed push :: events) =
      push.run.len :: formedLengths events := rfl

@[simp]
theorem formedLengths_merge (event : LogicalMergeEvent)
    (events : List PolicyEvent) :
    formedLengths (.merge event :: events) = formedLengths events := rfl

@[simp]
theorem logicalMergeCost_nil : logicalMergeCost [] = 0 := rfl

@[simp]
theorem logicalMergeCost_formed (push : PendingPushEvent)
    (events : List PolicyEvent) :
    logicalMergeCost (.formed push :: events) = logicalMergeCost events := rfl

@[simp]
theorem logicalMergeCost_merge (event : LogicalMergeEvent)
    (events : List PolicyEvent) :
    logicalMergeCost (.merge event :: events) =
      event.left.len + event.right.len + logicalMergeCost events := rfl

@[simp]
theorem logicalMergeCosts_nil : logicalMergeCosts [] = [] := rfl

@[simp]
theorem logicalMergeCosts_formed (push : PendingPushEvent)
    (events : List PolicyEvent) :
    logicalMergeCosts (.formed push :: events) = logicalMergeCosts events := rfl

@[simp]
theorem logicalMergeCosts_merge (event : LogicalMergeEvent)
    (events : List PolicyEvent) :
    logicalMergeCosts (.merge event :: events) =
      (event.left.len + event.right.len) :: logicalMergeCosts events := rfl

/-- Summing the chronological per-merge projection recovers the accounting
total exactly. -/
theorem logicalMergeCosts_sum (events : List PolicyEvent) :
    (logicalMergeCosts events).sum = logicalMergeCost events := by
  induction events with
  | nil => rfl
  | cons event events ih =>
      cases event <;> simp [ih]

theorem formedSpans_append (first second : List PolicyEvent) :
    formedSpans (first ++ second) = formedSpans first ++ formedSpans second := by
  induction first with
  | nil => rfl
  | cons event events ih =>
      cases event <;> simp [ih]

theorem formedLengths_append (first second : List PolicyEvent) :
    formedLengths (first ++ second) =
      formedLengths first ++ formedLengths second := by
  simp [formedLengths, formedSpans_append, List.map_append]

theorem logicalMergeCost_append (first second : List PolicyEvent) :
    logicalMergeCost (first ++ second) =
      logicalMergeCost first + logicalMergeCost second := by
  induction first with
  | nil => simp
  | cons event events ih =>
      cases event <;> simp [ih, Nat.add_assoc]

end PolicyEvent

/-! ## Forest invariants -/

namespace SpannedMergeTree

/-- Every leaf has positive length. -/
def Positive (entry : SpannedMergeTree) : Prop :=
  ∀ length ∈ entry.tree.runLengths, 0 < length

@[simp]
theorem leaf_positive_iff (span : RunSpan) :
    (leaf span).Positive ↔ 0 < span.len := by
  simp [Positive, leaf, MergeTree.runLengths]

theorem merge_positive (power : Nat) {left right : SpannedMergeTree}
    (hleft : left.Positive) (hright : right.Positive) :
    (merge power left right).Positive := by
  intro length hlength
  simp only [merge, MergeTree.runLengths, List.mem_append] at hlength
  exact hlength.elim (hleft length) (hright length)

end SpannedMergeTree

/-- Root spans in a forest are consecutive from left to right. -/
def AdjacentForest : List SpannedMergeTree → Prop
  | [] => True
  | [_] => True
  | left :: right :: rest =>
      left.span.Adjacent right.span ∧ AdjacentForest (right :: rest)

/-- The first root of a nonempty forest starts at `input.base`. -/
def ForestStartsAt (input : RunSpan) : List SpannedMergeTree → Prop
  | [] => True
  | first :: _ => first.span.base = input.base

/-- Every represented interval ends within the declared input interval. -/
def ForestWithin (input : RunSpan) (forest : List SpannedMergeTree) : Prop :=
  ∀ entry ∈ forest, entry.span.endIndex ≤ input.endIndex

/-- Replay invariant: valid positive trees forming an adjacent input prefix. -/
def PolicyForestInv (input : RunSpan)
    (forest : List SpannedMergeTree) : Prop :=
  (∀ entry ∈ forest, entry.Valid ∧ entry.Positive) ∧
    AdjacentForest forest ∧
    ForestStartsAt input forest ∧
    ForestWithin input forest

/-- Flatten the leaf lengths of an ordered merge forest. -/
def forestRunLengths (forest : List SpannedMergeTree) : List Nat :=
  forest.flatMap fun entry => entry.tree.runLengths

/-- Sum the already-incurred internal merge cost of a forest. -/
def forestMergeCost (forest : List SpannedMergeTree) : Nat :=
  (forest.map fun entry => entry.tree.mergeCost).sum

@[simp]
theorem forestRunLengths_nil : forestRunLengths [] = [] := rfl

@[simp]
theorem forestRunLengths_cons (entry : SpannedMergeTree)
    (forest : List SpannedMergeTree) :
    forestRunLengths (entry :: forest) =
      entry.tree.runLengths ++ forestRunLengths forest := rfl

@[simp]
theorem forestMergeCost_nil : forestMergeCost [] = 0 := rfl

@[simp]
theorem forestMergeCost_cons (entry : SpannedMergeTree)
    (forest : List SpannedMergeTree) :
    forestMergeCost (entry :: forest) =
      entry.tree.mergeCost + forestMergeCost forest := rfl

/-! ## Checked event semantics -/

/-- Exact adaptive-minrun relationship recorded by a formed-run event.

The first disjunct is the `naturalLength < target` branch: `binarysort`
extends the run to `min remainingBefore target`.  The second is the already
long natural-run branch, where the final run length is unchanged. -/
def FormedLengthRelation (push : PendingPushEvent) : Prop :=
  0 < push.naturalLength ∧
    push.naturalLength ≤ push.remainingBefore ∧
    0 < push.target ∧
    ((push.naturalLength < push.target ∧
        push.run.len = min push.remainingBefore push.target) ∨
      (push.target ≤ push.naturalLength ∧
        push.run.len = push.naturalLength))

instance (push : PendingPushEvent) : Decidable (FormedLengthRelation push) :=
  inferInstanceAs (Decidable
    (0 < push.naturalLength ∧ push.naturalLength ≤ push.remainingBefore ∧
      0 < push.target ∧
      ((push.naturalLength < push.target ∧
          push.run.len = min push.remainingBefore push.target) ∨
        (push.target ≤ push.naturalLength ∧
          push.run.len = push.naturalLength))))

/-- The base at which a new formed run must begin. -/
def nextForestBase (input : RunSpan)
    (forest : List SpannedMergeTree) : Nat :=
  match forest.getLast? with
  | none => input.base
  | some last => last.span.endIndex

/-- Full validation predicate for a formed-run event at one replay point. -/
def ValidFormedEvent (input : RunSpan) (forest : List SpannedMergeTree)
    (push : PendingPushEvent) : Prop :=
  push.depthAfter = forest.length + 1 ∧
    push.run.base = nextForestBase input forest ∧
    push.run.base + push.remainingBefore = input.endIndex ∧
    0 < push.run.len ∧
    push.run.len ≤ push.remainingBefore ∧
    FormedLengthRelation push

instance (input : RunSpan) (forest : List SpannedMergeTree)
    (push : PendingPushEvent) : Decidable (ValidFormedEvent input forest push) :=
  inferInstanceAs (Decidable
    (push.depthAfter = forest.length + 1 ∧
      push.run.base = nextForestBase input forest ∧
      push.run.base + push.remainingBefore = input.endIndex ∧
      0 < push.run.len ∧ push.run.len ≤ push.remainingBefore ∧
      FormedLengthRelation push))

/-- The exact transcribed node power belonging to two aggregate spans. -/
def replayBoundaryPower (input left right : RunSpan) : Nat :=
  powerloop (BitVec.ofNat 64 (left.base - input.base))
    (BitVec.ofNat 64 left.len) (BitVec.ofNat 64 right.len)
    (BitVec.ofNat 64 input.len)

/-- Apply one raw policy event to an ordered merge forest.

Formed-run metadata is checked before appending a leaf.  A merge checks both
pre-trim operand spans at the recorded index and checks adjacency before
splicing in a node labelled by `replayBoundaryPower`. -/
def applyPolicyEvent? (input : RunSpan)
    (forest : List SpannedMergeTree) :
    PolicyEvent → Option (List SpannedMergeTree)
  | .formed push =>
      if ValidFormedEvent input forest push then
        some (forest ++ [SpannedMergeTree.leaf push.run])
      else
        none
  | .merge event => do
      let left ← forest[event.index]?
      let right ← forest[event.index + 1]?
      if left.span = event.left ∧ right.span = event.right ∧
          event.left.Adjacent event.right then
        some (forest.take event.index ++
          SpannedMergeTree.merge
            (replayBoundaryPower input event.left event.right) left right ::
          forest.drop (event.index + 2))
      else
        none

/-- Replay a chronological, interleaved policy-event stream. -/
def replayPolicyEventsFrom? (input : RunSpan) :
    List SpannedMergeTree → List PolicyEvent →
      Option (List SpannedMergeTree)
  | forest, [] => some forest
  | forest, event :: events => do
      let forest ← applyPolicyEvent? input forest event
      replayPolicyEventsFrom? input forest events

/-- Replay a complete policy stream from the empty initial forest. -/
def replayPolicyEvents? (input : RunSpan)
    (events : List PolicyEvent) : Option (List SpannedMergeTree) :=
  replayPolicyEventsFrom? input [] events

/-- Exact success characterization for one formed-run event. -/
theorem applyPolicyEvent_formed_eq_some_iff
    (input : RunSpan) (forest result : List SpannedMergeTree)
    (push : PendingPushEvent) :
    applyPolicyEvent? input forest (.formed push) = some result ↔
      ValidFormedEvent input forest push ∧
        result = forest ++ [SpannedMergeTree.leaf push.run] := by
  simp [applyPolicyEvent?, eq_comm]

/-- Exact success characterization for one logical merge event. -/
theorem applyPolicyEvent_merge_eq_some_iff
    (input : RunSpan) (forest result : List SpannedMergeTree)
    (event : LogicalMergeEvent) :
    applyPolicyEvent? input forest (.merge event) = some result ↔
      ∃ left right,
        forest[event.index]? = some left ∧
        forest[event.index + 1]? = some right ∧
        left.span = event.left ∧
        right.span = event.right ∧
        event.left.Adjacent event.right ∧
        result = forest.take event.index ++
          SpannedMergeTree.merge
            (replayBoundaryPower input event.left event.right) left right ::
          forest.drop (event.index + 2) := by
  constructor
  · intro hresult
    cases hleft : forest[event.index]? with
    | none => simp [applyPolicyEvent?, hleft] at hresult
    | some left =>
        cases hright : forest[event.index + 1]? with
        | none => simp [applyPolicyEvent?, hleft, hright] at hresult
        | some right =>
            by_cases hcheck :
                left.span = event.left ∧ right.span = event.right ∧
                  event.left.Adjacent event.right
            · have hout :
                  forest.take event.index ++
                      SpannedMergeTree.merge
                        (replayBoundaryPower input event.left event.right)
                        left right :: forest.drop (event.index + 2) = result := by
                simpa [applyPolicyEvent?, hleft, hright, hcheck] using hresult
              exact ⟨left, right, rfl, rfl, hcheck.1, hcheck.2.1,
                hcheck.2.2, hout.symm⟩
            · simp [applyPolicyEvent?, hleft, hright, hcheck] at hresult
  · rintro ⟨left, right, hleft, hright, hleftSpan, hrightSpan,
      hadjacent, rfl⟩
    simp [applyPolicyEvent?, hleft, hright, hleftSpan, hrightSpan, hadjacent]

/-- Replaying concatenated event segments is exactly sequential replay. -/
theorem replayPolicyEventsFrom_append (input : RunSpan)
    (forest : List SpannedMergeTree) (first second : List PolicyEvent) :
    replayPolicyEventsFrom? input forest (first ++ second) =
      (replayPolicyEventsFrom? input forest first).bind fun middle =>
        replayPolicyEventsFrom? input middle second := by
  induction first generalizing forest with
  | nil => rfl
  | cons event events ih =>
      simp only [List.cons_append, replayPolicyEventsFrom?]
      cases hstep : applyPolicyEvent? input forest event with
      | none => simp
      | some middle => simpa using ih middle

/-- Success over a concatenated trace exposes the unique intermediate forest
at the segment boundary. -/
theorem replayPolicyEventsFrom_append_eq_some_iff
    (input : RunSpan) (forest result : List SpannedMergeTree)
    (first second : List PolicyEvent) :
    replayPolicyEventsFrom? input forest (first ++ second) = some result ↔
      ∃ middle,
        replayPolicyEventsFrom? input forest first = some middle ∧
          replayPolicyEventsFrom? input middle second = some result := by
  rw [replayPolicyEventsFrom_append]
  cases hfirst : replayPolicyEventsFrom? input forest first with
  | none => simp
  | some middle => simp

/-- Every formed-run observation accepted by a successful replay satisfies
the exact adaptive-minrun branch equation recorded in that observation.  This
exports the arithmetic check performed by `applyPolicyEvent?`; downstream
cost theorems therefore need not treat the trace metadata as trusted prose. -/
theorem replayPolicyEventsFrom_formedLengthRelation
    {input : RunSpan} {initial result : List SpannedMergeTree}
    {events : List PolicyEvent}
    (hreplay : replayPolicyEventsFrom? input initial events = some result) :
    ∀ push, .formed push ∈ events → FormedLengthRelation push := by
  induction events generalizing initial with
  | nil => simp
  | cons event events ih =>
      simp only [replayPolicyEventsFrom?] at hreplay
      cases hstep : applyPolicyEvent? input initial event with
      | none => simp [hstep] at hreplay
      | some middle =>
          rw [hstep] at hreplay
          intro push hpush
          simp only [List.mem_cons] at hpush
          rcases hpush with hhead | htail
          · cases event with
            | formed observed =>
                cases hhead
                exact
                  ((applyPolicyEvent_formed_eq_some_iff input initial middle
                    push).mp hstep).1.2.2.2.2.2
            | merge observed => contradiction
          · exact ih hreplay push htail

/-- Complete replay from the empty forest inherits the same per-event
adaptive-minrun equation. -/
theorem replayPolicyEvents_formedLengthRelation
    {input : RunSpan} {events : List PolicyEvent}
    {result : List SpannedMergeTree}
    (hreplay : replayPolicyEvents? input events = some result) :
    ∀ push, .formed push ∈ events → FormedLengthRelation push := by
  exact replayPolicyEventsFrom_formedLengthRelation hreplay

/-! ## Empty/single-root normalization -/

/-- Normalize a completed forest to the paper-facing empty-or-tree plan.

The empty forest is accepted only for an empty input.  A singleton is accepted
only when its root span is exactly the declared input span. -/
def normalizePolicyForest? (input : RunSpan) :
    List SpannedMergeTree → Option MergePlan
  | [] => if input.len = 0 then some .empty else none
  | [root] => if root.span = input then some (.tree root.tree) else none
  | _ => none

/-- Replay and normalize one complete policy trace. -/
def replayMergePlan? (input : RunSpan)
    (events : List PolicyEvent) : Option MergePlan := do
  let forest ← replayPolicyEvents? input events
  normalizePolicyForest? input forest

@[simp]
theorem normalizePolicyForest_empty (base : Nat) :
    normalizePolicyForest? { base := base, len := 0 } [] = some .empty := by
  simp [normalizePolicyForest?]

@[simp]
theorem replayMergePlan_empty (base : Nat) :
    replayMergePlan? { base := base, len := 0 } [] = some .empty := by
  simp [replayMergePlan?, replayPolicyEvents?, replayPolicyEventsFrom?]

theorem normalizePolicyForest_singleton (input : RunSpan)
    (root : SpannedMergeTree) (hspan : root.span = input) :
    normalizePolicyForest? input [root] = some (.tree root.tree) := by
  simp [normalizePolicyForest?, hspan]

/-! ## Replay preservation -/

private theorem forestRunLengths_append_leaf
    (forest : List SpannedMergeTree) (span : RunSpan) :
    forestRunLengths (forest ++ [SpannedMergeTree.leaf span]) =
      forestRunLengths forest ++ [span.len] := by
  simp [forestRunLengths, SpannedMergeTree.leaf, MergeTree.runLengths]

private theorem forestMergeCost_append_leaf
    (forest : List SpannedMergeTree) (span : RunSpan) :
    forestMergeCost (forest ++ [SpannedMergeTree.leaf span]) =
      forestMergeCost forest := by
  simp [forestMergeCost, SpannedMergeTree.leaf, MergeTree.mergeCost]

/- The splice lemmas below are stated from successful lookup equations.  This
keeps all index arithmetic local to replay and lets downstream users consume
the semantic equalities without reopening the implementation. -/

private theorem list_eq_take_append_get_drop_of_getElem?_eq_some
    {xs : List α} {i : Nat} {x : α} (h : xs[i]? = some x) :
    xs = xs.take i ++ x :: xs.drop (i + 1) := by
  have hi : i < xs.length := (List.getElem?_eq_some_iff.mp h).1
  have hdrop : xs.drop i = x :: xs.drop (i + 1) := by
    have hx : xs[i] = x := by
      simpa [List.getElem?_eq_getElem hi] using h
    rw [List.drop_eq_getElem_cons hi, hx]
  calc
    xs = xs.take i ++ xs.drop i := (List.take_append_drop i xs).symm
    _ = xs.take i ++ x :: xs.drop (i + 1) := by rw [hdrop]

private theorem replay_merge_decomposition
    {forest : List SpannedMergeTree} {event : LogicalMergeEvent}
    {left right : SpannedMergeTree}
    (hleft : forest[event.index]? = some left)
    (hright : forest[event.index + 1]? = some right) :
    forest = forest.take event.index ++
      left :: right :: forest.drop (event.index + 2) := by
  rcases List.getElem?_eq_some_iff.mp hleft with ⟨hi, hleftEq⟩
  rcases List.getElem?_eq_some_iff.mp hright with ⟨hiOne, hrightEq⟩
  calc
    forest = forest.take event.index ++ forest.drop event.index :=
      (List.take_append_drop event.index forest).symm
    _ = forest.take event.index ++
        forest[event.index] :: forest.drop (event.index + 1) := by
      rw [List.drop_eq_getElem_cons hi]
    _ = forest.take event.index ++
        left :: forest.drop (event.index + 1) := by rw [hleftEq]
    _ = forest.take event.index ++ left ::
        forest[event.index + 1] :: forest.drop (event.index + 2) := by
      rw [List.drop_eq_getElem_cons hiOne]
    _ = forest.take event.index ++
        left :: right :: forest.drop (event.index + 2) := by rw [hrightEq]

private theorem forestRunLengths_merge_splice
    (before after : List SpannedMergeTree)
    (left right : SpannedMergeTree) (power : Nat) :
    forestRunLengths
        (before ++ SpannedMergeTree.merge power left right :: after) =
      forestRunLengths (before ++ left :: right :: after) := by
  simp [forestRunLengths, SpannedMergeTree.merge, MergeTree.runLengths,
    List.append_assoc]

private theorem forestMergeCost_merge_splice
    (before after : List SpannedMergeTree)
    (left right : SpannedMergeTree) (power : Nat) :
    forestMergeCost
        (before ++ SpannedMergeTree.merge power left right :: after) =
      forestMergeCost (before ++ left :: right :: after) +
        left.tree.totalLength + right.tree.totalLength := by
  simp [forestMergeCost, SpannedMergeTree.merge, MergeTree.mergeCost]
  omega

theorem applyPolicyEvent_runLengths
    {input : RunSpan} {forest result : List SpannedMergeTree}
    {event : PolicyEvent}
    (hreplay : applyPolicyEvent? input forest event = some result) :
    forestRunLengths result =
      forestRunLengths forest ++ PolicyEvent.formedLengths [event] := by
  cases event with
  | formed push =>
      simp only [applyPolicyEvent?] at hreplay
      split at hreplay
      · have hresult := Option.some.inj hreplay
        subst result
        exact forestRunLengths_append_leaf forest push.run
      · simp at hreplay
  | merge event =>
      rcases (applyPolicyEvent_merge_eq_some_iff input forest result event).mp
          hreplay with
        ⟨left, right, hleft, hright, _, _, _, hresult⟩
      subst result
      rw [forestRunLengths_merge_splice]
      simp only [PolicyEvent.formedLengths_merge,
        PolicyEvent.formedLengths_nil, List.append_nil]
      exact congrArg forestRunLengths
        (replay_merge_decomposition hleft hright).symm

theorem applyPolicyEvent_cost
    {input : RunSpan} {forest result : List SpannedMergeTree}
    {event : PolicyEvent}
    (hinv : PolicyForestInv input forest)
    (hreplay : applyPolicyEvent? input forest event = some result) :
    forestMergeCost result =
      forestMergeCost forest + PolicyEvent.logicalMergeCost [event] := by
  cases event with
  | formed push =>
      simp only [applyPolicyEvent?] at hreplay
      split at hreplay
      · have hresult := Option.some.inj hreplay
        subst result
        exact forestMergeCost_append_leaf forest push.run
      · simp at hreplay
  | merge event =>
      rcases (applyPolicyEvent_merge_eq_some_iff input forest result event).mp
          hreplay with
        ⟨left, right, hleft, hright, hleftSpan, hrightSpan, _, hresult⟩
      subst result
      rcases List.getElem?_eq_some_iff.mp hleft with
        ⟨hleftBound, hleftEq⟩
      rcases List.getElem?_eq_some_iff.mp hright with
        ⟨hrightBound, hrightEq⟩
      have hleftMem : left ∈ forest :=
        List.mem_iff_getElem.mpr
          ⟨event.index, hleftBound, hleftEq⟩
      have hrightMem : right ∈ forest :=
        List.mem_iff_getElem.mpr
          ⟨event.index + 1, hrightBound, hrightEq⟩
      have hleftValid := (hinv.1 left hleftMem).1
      have hrightValid := (hinv.1 right hrightMem).1
      rw [forestMergeCost_merge_splice]
      have hdecompCost := congrArg forestMergeCost
        (replay_merge_decomposition hleft hright)
      rw [← hdecompCost]
      simp only [PolicyEvent.logicalMergeCost_merge,
        PolicyEvent.logicalMergeCost_nil, Nat.add_zero]
      simp only [SpannedMergeTree.Valid] at hleftValid hrightValid
      rw [hleftValid, hrightValid, hleftSpan, hrightSpan]
      omega

/-! The structural invariant proof is factored through two local preservation
lemmas. -/

private theorem adjacentForest_append_leaf
    {input : RunSpan} {forest : List SpannedMergeTree}
    {push : PendingPushEvent}
    (hadj : AdjacentForest forest)
    (hbase : push.run.base = nextForestBase input forest) :
    AdjacentForest (forest ++ [SpannedMergeTree.leaf push.run]) := by
  induction forest with
  | nil => simp [AdjacentForest]
  | cons first rest ih =>
      cases rest with
      | nil =>
          have hbase' : push.run.base = first.span.endIndex := by
            simpa [nextForestBase] using hbase
          change first.span.Adjacent (SpannedMergeTree.leaf push.run).span ∧ True
          constructor
          · change first.span.Adjacent push.run
            exact hbase'.symm
          · trivial
      | cons second tail =>
          simp only [AdjacentForest] at hadj ⊢
          exact ⟨hadj.1, ih hadj.2 hbase⟩

private theorem policyForestInv_append_leaf
    {input : RunSpan} {forest : List SpannedMergeTree}
    {push : PendingPushEvent}
    (hinv : PolicyForestInv input forest)
    (hvalid : ValidFormedEvent input forest push) :
    PolicyForestInv input (forest ++ [SpannedMergeTree.leaf push.run]) := by
  rcases hinv with ⟨htrees, hadj, hstarts, hwithin⟩
  rcases hvalid with
    ⟨_, hbase, hremaining, hpositive, hlenRemaining, _⟩
  refine ⟨?_, adjacentForest_append_leaf hadj hbase, ?_, ?_⟩
  · intro entry hentry
    rw [List.mem_append] at hentry
    rcases hentry with hentry | hentry
    · exact htrees entry hentry
    · simp only [List.mem_singleton] at hentry
      subst entry
      exact ⟨SpannedMergeTree.leaf_valid push.run,
        (SpannedMergeTree.leaf_positive_iff push.run).2 hpositive⟩
  · cases forest with
    | nil => simpa [ForestStartsAt, nextForestBase,
        SpannedMergeTree.leaf] using hbase
    | cons first rest => simpa [ForestStartsAt] using hstarts
  · intro entry hentry
    rw [List.mem_append] at hentry
    rcases hentry with hentry | hentry
    · exact hwithin entry hentry
    · simp only [List.mem_singleton] at hentry
      subst entry
      simp only [SpannedMergeTree.leaf]
      rw [RunSpan.endIndex]
      omega

private theorem span_adjacent_merge_left
    (power : Nat) {before left right : SpannedMergeTree}
    (h : before.span.Adjacent left.span) :
    before.span.Adjacent (SpannedMergeTree.merge power left right).span := by
  unfold RunSpan.Adjacent at h ⊢
  change before.span.endIndex = left.span.base at h
  change before.span.endIndex = left.span.base
  exact h

private theorem span_merge_adjacent_right
    (power : Nat) {left right after : SpannedMergeTree}
    (hlr : left.span.Adjacent right.span)
    (hra : right.span.Adjacent after.span) :
    (SpannedMergeTree.merge power left right).span.Adjacent after.span := by
  unfold RunSpan.Adjacent RunSpan.endIndex at hlr hra ⊢
  change left.span.base + (left.span.len + right.span.len) = after.span.base
  change left.span.base + left.span.len = right.span.base at hlr
  change right.span.base + right.span.len = after.span.base at hra
  omega

private theorem span_merge_endIndex
    (power : Nat) {left right : SpannedMergeTree}
    (hlr : left.span.Adjacent right.span) :
    (SpannedMergeTree.merge power left right).span.endIndex =
      right.span.endIndex := by
  change left.span.base + (left.span.len + right.span.len) =
    right.span.base + right.span.len
  unfold RunSpan.Adjacent RunSpan.endIndex at hlr
  change left.span.base + left.span.len = right.span.base at hlr
  omega

private theorem adjacentForest_merge_splice
    (power : Nat) (before after : List SpannedMergeTree)
    (left right : SpannedMergeTree)
    (hadj : AdjacentForest (before ++ left :: right :: after))
    (hlr : left.span.Adjacent right.span) :
    AdjacentForest
      (before ++ SpannedMergeTree.merge power left right :: after) := by
  induction before with
  | nil =>
      cases after with
      | nil => simp [AdjacentForest]
      | cons next tail =>
          simp only [List.nil_append, AdjacentForest] at hadj ⊢
          exact ⟨span_merge_adjacent_right power hlr hadj.2.1, hadj.2.2⟩
  | cons first before ih =>
      cases before with
      | nil =>
          simp only [List.cons_append, List.nil_append, AdjacentForest] at hadj ⊢
          refine ⟨span_adjacent_merge_left power hadj.1, ?_⟩
          cases after with
          | nil => simp [AdjacentForest]
          | cons next tail =>
              exact ⟨span_merge_adjacent_right power hlr hadj.2.2.1,
                hadj.2.2.2⟩
      | cons second tail =>
          simp only [List.cons_append, AdjacentForest] at hadj ⊢
          exact ⟨hadj.1, ih hadj.2⟩

private theorem policyForestInv_merge_splice
    {input : RunSpan} {before after : List SpannedMergeTree}
    {left right : SpannedMergeTree} {power : Nat}
    (hinv : PolicyForestInv input (before ++ left :: right :: after))
    (hadjacent : left.span.Adjacent right.span) :
    PolicyForestInv input
      (before ++ SpannedMergeTree.merge power left right :: after) := by
  rcases hinv with ⟨htrees, hadj, hstarts, hwithin⟩
  have hleftMem : left ∈ before ++ left :: right :: after := by simp
  have hrightMem : right ∈ before ++ left :: right :: after := by simp
  have hleft := htrees left hleftMem
  have hright := htrees right hrightMem
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro entry hentry
    simp only [List.mem_append, List.mem_cons] at hentry
    rcases hentry with hbefore | hmerged | hafter
    · exact htrees entry (by simp [hbefore])
    · subst entry
      exact ⟨SpannedMergeTree.merge_valid power hleft.1 hright.1,
        SpannedMergeTree.merge_positive power hleft.2 hright.2⟩
    · exact htrees entry (by simp [hafter])
  · exact adjacentForest_merge_splice power before after left right hadj hadjacent
  · cases before with
    | nil => simpa [ForestStartsAt, SpannedMergeTree.merge, RunSpan.merge] using hstarts
    | cons first rest => simpa [ForestStartsAt] using hstarts
  · intro entry hentry
    simp only [List.mem_append, List.mem_cons] at hentry
    rcases hentry with hbefore | hmerged | hafter
    · exact hwithin entry (by simp [hbefore])
    · subst entry
      have hrightWithin := hwithin right hrightMem
      rw [span_merge_endIndex power hadjacent]
      exact hrightWithin
    · exact hwithin entry (by simp [hafter])

theorem applyPolicyEvent_preserves_inv
    {input : RunSpan} {forest result : List SpannedMergeTree}
    {event : PolicyEvent}
    (hinv : PolicyForestInv input forest)
    (hreplay : applyPolicyEvent? input forest event = some result) :
    PolicyForestInv input result := by
  cases event with
  | formed push =>
      simp only [applyPolicyEvent?] at hreplay
      split at hreplay
      · rename_i hvalid
        simp only [Option.some.injEq] at hreplay
        subst result
        exact policyForestInv_append_leaf hinv hvalid
      · simp at hreplay
  | merge event =>
      rcases (applyPolicyEvent_merge_eq_some_iff input forest result event).mp
          hreplay with
        ⟨left, right, hleft, hright, hleftSpan, hrightSpan,
          heventAdjacent, hresult⟩
      subst result
      rw [replay_merge_decomposition hleft hright] at hinv
      have hactual : left.span.Adjacent right.span := by
        rw [hleftSpan, hrightSpan]
        exact heventAdjacent
      exact policyForestInv_merge_splice
        (power := replayBoundaryPower input event.left event.right)
        hinv hactual

theorem replayPolicyEventsFrom_runLengths
    {input : RunSpan} {initial result : List SpannedMergeTree}
    {events : List PolicyEvent}
    (hreplay : replayPolicyEventsFrom? input initial events = some result) :
    forestRunLengths result =
      forestRunLengths initial ++ PolicyEvent.formedLengths events := by
  induction events generalizing initial with
  | nil =>
      simp only [replayPolicyEventsFrom?, Option.some.injEq] at hreplay
      subst result
      simp
  | cons event events ih =>
      simp only [replayPolicyEventsFrom?] at hreplay
      cases hstep : applyPolicyEvent? input initial event with
      | none => simp [hstep] at hreplay
      | some middle =>
          rw [hstep] at hreplay
          have hfirst := applyPolicyEvent_runLengths hstep
          have hrest := ih hreplay
          rw [hrest, hfirst]
          cases event <;> simp [List.append_assoc]

theorem replayPolicyEventsFrom_preserves_inv
    {input : RunSpan} {initial result : List SpannedMergeTree}
    {events : List PolicyEvent}
    (hinv : PolicyForestInv input initial)
    (hreplay : replayPolicyEventsFrom? input initial events = some result) :
    PolicyForestInv input result := by
  induction events generalizing initial with
  | nil =>
      simp only [replayPolicyEventsFrom?, Option.some.injEq] at hreplay
      subst result
      exact hinv
  | cons event events ih =>
      simp only [replayPolicyEventsFrom?] at hreplay
      cases hstep : applyPolicyEvent? input initial event with
      | none => simp [hstep] at hreplay
      | some middle =>
          rw [hstep] at hreplay
          exact ih (applyPolicyEvent_preserves_inv hinv hstep) hreplay

theorem replayPolicyEventsFrom_cost
    {input : RunSpan} {initial result : List SpannedMergeTree}
    {events : List PolicyEvent}
    (hinv : PolicyForestInv input initial)
    (hreplay : replayPolicyEventsFrom? input initial events = some result) :
    forestMergeCost result =
      forestMergeCost initial + PolicyEvent.logicalMergeCost events := by
  induction events generalizing initial with
  | nil =>
      simp only [replayPolicyEventsFrom?, Option.some.injEq] at hreplay
      subst result
      simp
  | cons event events ih =>
      simp only [replayPolicyEventsFrom?] at hreplay
      cases hstep : applyPolicyEvent? input initial event with
      | none => simp [hstep] at hreplay
      | some middle =>
          rw [hstep] at hreplay
          have hmiddle := applyPolicyEvent_preserves_inv hinv hstep
          have hfirst := applyPolicyEvent_cost hinv hstep
          have hrest := ih hmiddle hreplay
          rw [hrest, hfirst]
          cases event <;> simp
          omega

@[simp]
theorem policyForestInv_empty (input : RunSpan) :
    PolicyForestInv input [] := by
  simp [PolicyForestInv, AdjacentForest, ForestStartsAt, ForestWithin]

/-- Every successful replay from the empty forest preserves positive trees,
valid span lengths, adjacency, the input start, and input containment. -/
theorem replayPolicyEvents_preserves_partition
    {input : RunSpan} {events : List PolicyEvent}
    {result : List SpannedMergeTree}
    (hreplay : replayPolicyEvents? input events = some result) :
    PolicyForestInv input result := by
  exact replayPolicyEventsFrom_preserves_inv (policyForestInv_empty input) hreplay

/-- Successful replay preserves formed-run leaf order exactly. -/
theorem replayPolicyEvents_runLengths
    {input : RunSpan} {events : List PolicyEvent}
    {result : List SpannedMergeTree}
    (hreplay : replayPolicyEvents? input events = some result) :
    forestRunLengths result = PolicyEvent.formedLengths events := by
  simpa [replayPolicyEvents?, forestRunLengths] using
    replayPolicyEventsFrom_runLengths hreplay

/-- Successful replay accumulates exactly the logical pre-trimming merge cost. -/
theorem replayPolicyEvents_cost
    {input : RunSpan} {events : List PolicyEvent}
    {result : List SpannedMergeTree}
    (hreplay : replayPolicyEvents? input events = some result) :
    forestMergeCost result = PolicyEvent.logicalMergeCost events := by
  simpa [replayPolicyEvents?, forestMergeCost] using
    replayPolicyEventsFrom_cost (policyForestInv_empty input) hreplay

/-- A complete replay to one root has exactly the formed-run leaves and the
logical event cost recorded by the trace. -/
theorem completePolicyReplay_exact
    {input : RunSpan} {events : List PolicyEvent}
    {root : SpannedMergeTree}
    (hreplay : replayPolicyEvents? input events = some [root]) :
    root.tree.runLengths = PolicyEvent.formedLengths events ∧
      root.tree.mergeCost = PolicyEvent.logicalMergeCost events := by
  constructor
  · simpa [forestRunLengths] using replayPolicyEvents_runLengths hreplay
  · simpa [forestMergeCost] using replayPolicyEvents_cost hreplay

/-- A normalized successful plan exposes the same formed leaves and exact
logical merge cost; this includes the empty-input case. -/
theorem replayMergePlan_exact
    {input : RunSpan} {events : List PolicyEvent} {plan : MergePlan}
    (hreplay : replayMergePlan? input events = some plan) :
    plan.runLengths = PolicyEvent.formedLengths events ∧
      plan.mergeCost = PolicyEvent.logicalMergeCost events := by
  unfold replayMergePlan? at hreplay
  cases hforest : replayPolicyEvents? input events with
  | none => simp [hforest] at hreplay
  | some forest =>
      rw [hforest] at hreplay
      cases forest with
      | nil =>
          change (if input.len = 0 then some .empty else none) = some plan at hreplay
          split at hreplay
          · simp only [Option.some.injEq] at hreplay
            subst plan
            have hlengths := replayPolicyEvents_runLengths hforest
            have hcost := replayPolicyEvents_cost hforest
            simpa [forestRunLengths, forestMergeCost, MergePlan.runLengths,
              MergePlan.mergeCost] using And.intro hlengths hcost
          · simp at hreplay
      | cons root rest =>
          cases rest with
          | nil =>
              change (if root.span = input then some (.tree root.tree) else none) =
                some plan at hreplay
              split at hreplay
              · simp only [Option.some.injEq] at hreplay
                subst plan
                exact completePolicyReplay_exact hforest
              · simp at hreplay
          | cons second tail => simp [normalizePolicyForest?] at hreplay

end CPythonListsort
