/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Assembly.PowerSortPolicyCost
import Code.Policy.StackPowers

/-!
# Historical PowerSort invariant for the open scan forest

The machine's pending stack remembers only the power on each open boundary.
It does not remember the internal heap edges of subtrees that have already
been merged.  This module supplies the missing historical invariant carried
by the scan proof: every replay root is aligned with one pending run, is a
source-faithful power tree, and places its outgoing stored boundary below its
internal root power.  The newest root is explicitly a leaf, matching
`found_new_run`'s merge-before-push control flow.

No evaluator induction appears here.  A later bridge must prove preservation
of this invariant from the actual `found_new_run` trace.
-/

namespace CPythonListsort

universe u v

/-- Historical facts connecting one open replay root to its current pending
run.  The final clause is vacuous for a leaf and records the heap edge that is
otherwise lost when an internal subtree is summarized by one pending run. -/
structure RunTreeAligned (input : RunSpan) (entry : SpannedMergeTree)
    (run : PendingRun) : Prop where
  span_eq : entry.span = RunSpan.ofPendingRun run
  valid : entry.Valid
  powerValid : entry.tree.PowerValid input.base
    (BitVec.ofNat 64 input.len) entry.span.base
  outgoingBelowRoot : ∀ boundaryPower rootPower,
    run.power = some boundaryPower →
      entry.tree.rootPower = some rootPower → boundaryPower < rootPower

/-- The final root of a nonempty open forest is a literal leaf.  The custom
inductive form makes preservation by prepending older roots explicit, while
also admitting the empty initial forest. -/
inductive NewestRootLeaf : List SpannedMergeTree → Prop
  | empty : NewestRootLeaf []
  | singleton (span : RunSpan) :
      NewestRootLeaf [SpannedMergeTree.leaf span]
  | prepend (entry right : SpannedMergeTree)
      (rest : List SpannedMergeTree)
      (tail : NewestRootLeaf (right :: rest)) :
      NewestRootLeaf (entry :: right :: rest)

/-- The scan-carried historical certificate for an open merge forest.

`basekeys_eq` and `listlen_eq` are the exact machine/input frame.  `aligned`
keeps forest roots and pending runs in lockstep; unlike a span-only matching
predicate, it retains each root's internal PowerSort validity and the missing
heap edge from the outgoing pending power into that root. -/
structure ScanPowerForestInv (input : RunSpan)
    (forest : List SpannedMergeTree) (state : MergeState κ ν) : Prop where
  inputMax : input.len ≤ PY_LIST_MAX
  basekeys_eq : state.basekeys = input.base
  listlen_eq : state.listlen = BitVec.ofNat 64 input.len
  aligned : List.Forall₂ (RunTreeAligned input) forest state.pending.toList
  newestRootLeaf : NewestRootLeaf forest

namespace ScanPowerForestInv

private theorem spans_eq_of_aligned
    {input : RunSpan} {forest : List SpannedMergeTree}
    {runs : List PendingRun}
    (h : List.Forall₂ (RunTreeAligned input) forest runs) :
    forest.map SpannedMergeTree.span = runs.map RunSpan.ofPendingRun := by
  induction h with
  | nil => rfl
  | cons haligned _ ih =>
      simp only [List.map_cons, List.cons.injEq]
      exact ⟨haligned.span_eq, ih⟩

/-- The historical alignment projects to the span equality used by policy
replay and collapse bridges. -/
theorem spans_eq_pending
    {input : RunSpan} {forest : List SpannedMergeTree}
    {state : MergeState κ ν}
    (h : ScanPowerForestInv input forest state) :
    forest.map SpannedMergeTree.span =
      state.pending.toList.map RunSpan.ofPendingRun := by
  exact spans_eq_of_aligned h.aligned

/-- Forest and pending stack have exactly the same number of open roots. -/
theorem length_eq_pending
    {input : RunSpan} {forest : List SpannedMergeTree}
    {state : MergeState κ ν}
    (h : ScanPowerForestInv input forest state) :
    forest.length = state.pending.size := by
  simpa using h.aligned.length_eq

/-- Every displayed open root is a valid source-faithful PowerSort tree. -/
private theorem tree_valid_of_aligned
    {input : RunSpan} {forest : List SpannedMergeTree}
    {runs : List PendingRun}
    (h : List.Forall₂ (RunTreeAligned input) forest runs)
    {entry : SpannedMergeTree} (hentry : entry ∈ forest) :
    entry.Valid ∧
      entry.tree.PowerValid input.base (BitVec.ofNat 64 input.len)
        entry.span.base := by
  induction h with
  | nil => simp at hentry
  | @cons head run forest runs hhead htail ih =>
      simp only [List.mem_cons] at hentry
      rcases hentry with rfl | hentry
      · exact ⟨hhead.valid, hhead.powerValid⟩
      · exact ih hentry

theorem tree_valid
    {input : RunSpan} {forest : List SpannedMergeTree}
    {state : MergeState κ ν}
    (h : ScanPowerForestInv input forest state)
    {entry : SpannedMergeTree} (hentry : entry ∈ forest) :
    entry.Valid ∧
      entry.tree.PowerValid input.base (BitVec.ofNat 64 input.len)
        entry.span.base := by
  exact tree_valid_of_aligned h.aligned hentry

private theorem openSpanChain_of_cover
    {input : RunSpan} {cursor limit : Nat}
    {forest : List SpannedMergeTree} {runs : List PendingRun}
    (hcursor : input.base ≤ cursor)
    (hlimit : limit = input.endIndex)
    (hcover : PendingRunsCover cursor limit runs)
    (haligned : List.Forall₂ (RunTreeAligned input) forest runs) :
    OpenSpanChain input cursor forest := by
  induction haligned generalizing cursor with
  | nil =>
      exact .empty (by simpa [PendingRunsCover, hlimit] using hcover)
  | @cons entry run forest runs hentry _ ih =>
      rcases hcover with
        ⟨hbase, hnonnegative, hpositive, hwithin, htail⟩
      have hentryBase : entry.span.base = cursor := by
        rw [hentry.span_eq]
        simpa [RunSpan.ofPendingRun] using hbase
      have hentryValid : entry.span.ValidWithin input := by
        rw [hentry.span_eq]
        refine ⟨?_, ?_, ?_⟩
        · simpa [RunSpan.ofPendingRun, hbase] using hcursor
        · simpa [RunSpan.ofPendingRun, RunSpan.endIndex,
            PendingRun.endIndex, hlimit] using hwithin
        · simpa [RunSpan.ofPendingRun] using hpositive
      apply OpenSpanChain.cons entry forest hentryBase hentryValid
      have hend : entry.span.endIndex = run.endIndex := by
        simp [hentry.span_eq, RunSpan.ofPendingRun, RunSpan.endIndex,
          PendingRun.endIndex]
      rw [hend]
      apply ih
      · simp only [PendingRun.endIndex]
        omega
      · exact htail

/-- Pending layout plus exact frame turns aligned roots into the explicit
positive adjacent input partition consumed by the pure open-forest theorem. -/
theorem openSpanChain
    {input : RunSpan} {forest : List SpannedMergeTree}
    {state : MergeState κ ν}
    (h : ScanPowerForestInv input forest state)
    (hlayout : PendingLayout state input.len) :
    OpenSpanChain input input.base forest := by
  apply openSpanChain_of_cover
    (input := input) (cursor := input.base)
    (limit := state.basekeys + input.len)
    (runs := state.pending.toList)
  · exact Nat.le_refl _
  · simp [RunSpan.endIndex, h.basekeys_eq]
  · simpa [h.basekeys_eq] using hlayout.2.2.2
  · exact h.aligned

private theorem replayBoundaryPower_eq_pendingBoundaryPower
    {input : RunSpan} {state : MergeState κ ν}
    {left right : SpannedMergeTree} {leftRun rightRun : PendingRun}
    (hbase : state.basekeys = input.base)
    (hlength : state.listlen = BitVec.ofNat 64 input.len)
    (hleft : RunTreeAligned input left leftRun)
    (hright : RunTreeAligned input right rightRun) :
    replayBoundaryPower input left.span right.span =
      pendingBoundaryPower state.basekeys state.listlen leftRun rightRun := by
  simp [replayBoundaryPower, pendingBoundaryPower, hbase, hlength,
    hleft.span_eq, hright.span_eq, RunSpan.ofPendingRun]

private theorem openBoundaryCertificate_of_aligned
    {input : RunSpan} {state : MergeState κ ν}
    {forest : List SpannedMergeTree} {runs : List PendingRun}
    {powers : List Nat}
    (hbase : state.basekeys = input.base)
    (hlength : state.listlen = BitVec.ofNat 64 input.len)
    (haligned : List.Forall₂ (RunTreeAligned input) forest runs)
    (hnewest : NewestRootLeaf forest)
    (hpowerMap : runs.dropLast.map PendingRun.power = powers.map some)
    (hexact : ExactBoundaryPowers state.basekeys state.listlen runs) :
    OpenBoundaryCertificate input forest powers := by
  induction hnewest generalizing runs powers with
  | empty =>
      cases haligned
      cases powers with
      | nil => exact .empty
      | cons power powers => cases hpowerMap
  | singleton span =>
      cases haligned with
      | cons hentry htail =>
          cases htail
          cases powers with
          | nil =>
              exact .singleton (SpannedMergeTree.leaf span) span.len rfl
          | cons power powers => cases hpowerMap
  | prepend entry right rest htail ih =>
      cases haligned with
      | @cons _ leftRun _ runs hleft halignedTail =>
          cases halignedTail with
          | @cons _ rightRun _ remainingRuns hright halignedRest =>
              cases powers with
              | nil => cases hpowerMap
              | cons power powers =>
                  simp only [List.dropLast_cons_cons, List.map_cons,
                    List.cons.injEq] at hpowerMap
                  rcases hpowerMap with ⟨hleftPower, hpowerTail⟩
                  have hhead := ExactBoundaryPowers.head hexact
                  have hexactTail := ExactBoundaryPowers.tail hexact
                  refine .cons entry right rest power powers ?_ ?_ ?_
                  · calc
                      power = pendingBoundaryPower state.basekeys state.listlen
                          leftRun rightRun := by
                            rw [hleftPower] at hhead
                            exact Option.some.inj hhead
                      _ = replayBoundaryPower input entry.span right.span :=
                        (replayBoundaryPower_eq_pendingBoundaryPower
                          hbase hlength hleft hright).symm
                  · intro rootPower hroot
                    exact hleft.outgoingBelowRoot power rootPower
                      hleftPower hroot
                  · exact ih (List.Forall₂.cons hright halignedRest)
                      hpowerTail hexactTail

/-- The boundary powers witnessing a powered pending prefix also certify the
exact open-forest boundaries and every historical heap edge. -/
theorem openBoundaryCertificate
    {input : RunSpan} {forest : List SpannedMergeTree}
    {state : MergeState κ ν}
    (h : ScanPowerForestInv input forest state)
    (hpowered : PoweredPrefix state) :
    ∃ powers,
      OpenBoundaryCertificate input forest powers ∧
        powers.Pairwise (fun earlier later => earlier < later) := by
  by_cases hempty : state.pending.toList = []
  · have hforest : forest = [] := by
      have hlength := h.aligned.length_eq
      rw [hempty] at hlength
      exact List.eq_nil_of_length_eq_zero (by simpa using hlength)
    subst forest
    exact ⟨[], .empty, by simp⟩
  · rcases hpowered.split_of_nonempty hempty with
      ⟨olderRuns, newest, hruns, hincreasing, hexact⟩
    rcases hincreasing with ⟨powers, hpowerMap, _hrange, hstrict⟩
    refine ⟨powers, ?_, hstrict⟩
    apply openBoundaryCertificate_of_aligned
      h.basekeys_eq h.listlen_eq h.aligned h.newestRootLeaf
    · rw [hruns]
      simpa using hpowerMap
    · exact hexact

/-- The scan-carried historical invariant, together with the already-proved
machine layout and powered-prefix invariants, yields the pure open PowerSort
forest certificate. -/
theorem toPowerOpenForestValid
    {input : RunSpan} {forest : List SpannedMergeTree}
    {state : MergeState κ ν}
    (h : ScanPowerForestInv input forest state)
    (hlayout : PendingLayout state input.len)
    (hpowered : PoweredPrefix state) :
    PowerOpenForestValid input forest := by
  rcases h.openBoundaryCertificate hpowered with
    ⟨powers, hboundaries, hstrict⟩
  exact ⟨powers,
    { inputMax := h.inputMax
      spans := h.openSpanChain hlayout
      treeValid := fun entry hentry => h.tree_valid hentry
      boundaries := hboundaries
      strict := hstrict }⟩

end ScanPowerForestInv

end CPythonListsort
