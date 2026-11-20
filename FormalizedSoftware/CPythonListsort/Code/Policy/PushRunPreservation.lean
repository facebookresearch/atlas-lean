/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Assembly.AccessTrace
import Code.Policy.StackDepth

/-!
# Policy preservation across the pending-run push

The caller of `found_new_run` performs an unconditional `Array.push`.  Given
the policy facts established just before that call site, this file proves that
the enlarged stack tiles the enlarged scanned prefix and again has a
`PoweredPrefix`: all old entries form the initialized prefix and the new top's
stored power remains deliberately unconstrained.

The operation itself is total on every modeled state.  `ReadyToPush` appears
only on the preservation and capacity theorem; it is not consulted by either
the ordinary or traced implementation.
-/

namespace CPythonListsort

universe u v

/-- Appending one adjacent positive run extends exact interval coverage by
that run's length. -/
theorem PendingRunsCover.appendSingleton
    {cursor limit : Nat} {runs : List PendingRun} {newRun : PendingRun}
    (hcover : PendingRunsCover cursor limit runs)
    (hbase : newRun.base = limit)
    (hnonnegative : newRun.len.Nonnegative)
    (hpositive : 0 < newRun.len.toNat) :
    PendingRunsCover cursor (limit + newRun.len.toNat) (runs ++ [newRun]) := by
  induction runs generalizing cursor with
  | nil =>
      simp only [PendingRunsCover] at hcover
      subst cursor
      simp [PendingRunsCover, PendingRun.endIndex, hbase, hnonnegative,
        hpositive]
  | cons run runs ih =>
      simp only [List.cons_append, PendingRunsCover] at hcover ⊢
      rcases hcover with
        ⟨hrunBase, hrunNonnegative, hrunPositive, hrunEnd, hrest⟩
      refine
        ⟨hrunBase, hrunNonnegative, hrunPositive, ?_,
          ih hrest⟩
      omega

/-- The unconditional source push extends the valid pending tiling by exactly
the newly discovered adjacent run. -/
theorem pushPendingRun_preserves_pendingLayout
    (state : MergeState κ ν) (scanned : Nat) (newRun : PendingRun)
    (hready : ReadyToPush state scanned newRun) :
    PendingLayout (pushPendingRun state newRun)
      (scanned + newRun.len.toNat) := by
  rcases hready.layout with
    ⟨hlistNonnegative, hdataBound, hscanned, hcover⟩
  rcases hready.new_run_nonempty with ⟨hnewNonnegative, hnewPositive⟩
  have hcover' := hcover.appendSingleton hready.new_run_adjacent
    hnewNonnegative hnewPositive
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [pushPendingRun] using hlistNonnegative
  · simpa [pushPendingRun] using hdataBound
  · simpa [pushPendingRun] using hready.new_run_within_input
  · simpa [pushPendingRun, Nat.add_assoc] using hcover'

/-- After the push, every former stack entry is in the initialized power
prefix and the new physical top is the unique entry whose stored power is not
constrained.  Exact boundary labels are transported directly from the virtual
post-push list in `ReadyToPush`. -/
theorem pushPendingRun_restores_poweredPrefix
    (state : MergeState κ ν) (scanned : Nat) (newRun : PendingRun)
    (hready : ReadyToPush state scanned newRun) :
    PoweredPrefix (pushPendingRun state newRun) := by
  right
  refine
    ⟨state.pending.toList, newRun, ?_, hready.current_powers, ?_⟩
  · simp [pushPendingRun]
  · simpa [pushPendingRun] using hready.virtual_boundary_powers

/-- Full policy postcondition of the actual `list_sort_impl` push.  The
operation mutates unconditionally; the premise proves properties of that
result, including the concrete release-build capacity bound. -/
theorem pushPendingRun_preserves_policy
    (state : MergeState κ ν) (scanned : Nat) (newRun : PendingRun)
    (hready : ReadyToPush state scanned newRun) :
    let pushed := pushPendingRun state newRun
    pushed.pending.toList = state.pending.toList ++ [newRun] ∧
      PendingLayout pushed (scanned + newRun.len.toNat) ∧
      PoweredPrefix pushed ∧
      pushed.pending.size = state.pending.size + 1 ∧
      pushed.pending.size ≤ 61 ∧
      pushed.pending.size < MAX_MERGE_PENDING := by
  dsimp only
  have hdepth := readyToPush_stack_depth_bound state scanned newRun hready
  exact
    ⟨by simp [pushPendingRun],
      pushPendingRun_preserves_pendingLayout state scanned newRun hready,
      pushPendingRun_restores_poweredPrefix state scanned newRun hready,
      hdepth.2.1, hdepth.2.2.1, hdepth.2.2.2⟩

/-- The traced wrapper is definitionally the same unconditional state update
as `pushPendingRun`, and records its exact post-push depth.  This theorem has
no policy or capacity premise. -/
theorem pushPendingRunTraced_is_total
    (state : MergeState κ ν) (newRun : PendingRun) :
    (pushPendingRunTraced state newRun).result =
        some (pushPendingRun state newRun) ∧
      (pushPendingRunTraced state newRun).trace.pushDepths =
        [state.pending.size + 1] ∧
      (pushPendingRunTraced state newRun).trace.stackDepthMax =
        state.pending.size + 1 := by
  simp [pushPendingRunTraced, pushPendingRun, AccessTrace.singletonPushDepth,
    AccessTrace.stackDepthMax]

/-- Traced form of the complete push postcondition.  In particular, the trace
records the same concrete depth that the preservation theorem proves to be at
most 61 and strictly below 64. -/
theorem pushPendingRunTraced_preserves_policy
    (state : MergeState κ ν) (scanned : Nat) (newRun : PendingRun)
    (hready : ReadyToPush state scanned newRun) :
    let traced := pushPendingRunTraced state newRun
    traced.result = some (pushPendingRun state newRun) ∧
      traced.trace.pushDepths = [state.pending.size + 1] ∧
      traced.trace.stackDepthMax = state.pending.size + 1 ∧
      traced.trace.stackDepthMax ≤ 61 ∧
      traced.trace.stackDepthMax < MAX_MERGE_PENDING ∧
      PendingLayout (pushPendingRun state newRun)
        (scanned + newRun.len.toNat) ∧
      PoweredPrefix (pushPendingRun state newRun) := by
  dsimp only
  have htotal := pushPendingRunTraced_is_total state newRun
  have hpolicy := pushPendingRun_preserves_policy state scanned newRun hready
  have hdepth := readyToPush_stack_depth_bound state scanned newRun hready
  refine
    ⟨htotal.1, htotal.2.1, htotal.2.2, ?_, ?_, hpolicy.2.1,
      hpolicy.2.2.1⟩
  · rw [htotal.2.2]
    rw [← hdepth.2.1]
    exact hdepth.2.2.1
  · rw [htotal.2.2]
    rw [← hdepth.2.1]
    exact hdepth.2.2.2

end CPythonListsort
