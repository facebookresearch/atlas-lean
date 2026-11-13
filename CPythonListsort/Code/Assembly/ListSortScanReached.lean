/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Assembly.ListSortTrace

/-!
# Control-flow provenance for the final-collapse call

The logical policy-event projection does not retain the machine state passed
to `merge_force_collapse`.  This module records that state separately, by
following the successful `TraceResult.bind` path of the genuine traced scan.
The certificate is intentionally independent of policy events: policy-free
helper prefixes can wrap it only when their actual result selects the certified
continuation.
-/

namespace CPythonListsort

universe u v

variable {κ : Type u} {ν : Type v}

/-- `openState` is the actual state at a successful terminal scan call, hence
the state passed by that call to `mergeForceCollapseTraced?`.

`bindPrefix` preserves this provenance through a genuine successful helper
prefix.  In particular, it cannot transport the certificate merely because
two executions happen to have equal policy-event projections. -/
inductive ListSortScanReachedCollapse
    (reverse : Bool) (inputSize : Nat)
    (openState : MergeState κ ν)
    (collapsed : MergeForceCollapseResult κ ν) :
    TraceResult (ListSortImplResult κ ν) → Prop where
  | terminal (fuel lo : Nat)
      (hcollapse :
        (mergeForceCollapseTraced? openState).result = some collapsed)
      (hcode : collapsed.returnCode = 0)
      (hfuel : collapsed.fuelExhausted = false) :
      ListSortScanReachedCollapse reverse inputSize openState collapsed
        (listSortScanTraced? fuel openState lo 0 reverse inputSize)
  | bindPrefix {α : Type (max u v)}
      (before : TraceResult α)
      (next : α → TraceResult (ListSortImplResult κ ν))
      (value : α)
      (hbefore : before.result = some value)
      (tail :
        ListSortScanReachedCollapse reverse inputSize openState collapsed
          (next value)) :
      ListSortScanReachedCollapse reverse inputSize openState collapsed
        (before.bind next)
  | prependMemoryEvent
      (execution : TraceResult (ListSortImplResult κ ν))
      (event : MergeMemoryEvent)
      (tail :
        ListSortScanReachedCollapse reverse inputSize openState collapsed
          execution) :
      ListSortScanReachedCollapse reverse inputSize openState collapsed
        (execution.prependMemoryEvent event)

namespace ListSortScanReachedCollapse

/-- Rewrite only the complete traced execution while retaining the exact
control-flow certificate.  This is deliberately stronger than equality of
the policy-event projection. -/
theorem of_execution_eq
    {reverse : Bool} {inputSize : Nat}
    {openState : MergeState κ ν}
    {collapsed : MergeForceCollapseResult κ ν}
    {first second : TraceResult (ListSortImplResult κ ν)}
    (reached :
      ListSortScanReachedCollapse reverse inputSize openState collapsed first)
    (hExecution : first = second) :
    ListSortScanReachedCollapse reverse inputSize openState collapsed second := by
  subst second
  exact reached

/-- A successful prefix may be placed in front of a certified execution.
Unlike policy-event transport, the result equation identifies the exact value
with which the continuation is entered. -/
theorem through_bind
    {reverse : Bool} {inputSize : Nat}
    {openState : MergeState κ ν}
    {collapsed : MergeForceCollapseResult κ ν}
    {α : Type (max u v)}
    (before : TraceResult α)
    (next : α → TraceResult (ListSortImplResult κ ν))
    (value : α)
    (hbefore : before.result = some value)
    (tail :
      ListSortScanReachedCollapse reverse inputSize openState collapsed
        (next value)) :
    ListSortScanReachedCollapse reverse inputSize openState collapsed
      (before.bind next) :=
  .bindPrefix before next value hbefore tail

/-- The certificate always exposes the successful result of the exact
`mergeForceCollapseTraced? openState` call reached at its terminal scan arm. -/
theorem collapse_result_eq
    {reverse : Bool} {inputSize : Nat}
    {openState : MergeState κ ν}
    {collapsed : MergeForceCollapseResult κ ν}
    {execution : TraceResult (ListSortImplResult κ ν)}
    (reached :
      ListSortScanReachedCollapse reverse inputSize openState collapsed
        execution) :
    (mergeForceCollapseTraced? openState).result = some collapsed := by
  induction reached with
  | terminal _ _ hcollapse _ _ => exact hcollapse
  | bindPrefix _ _ _ _ _ ih => exact ih
  | prependMemoryEvent _ _ _ ih => exact ih

/-- The collapse result named by a provenance certificate is a successful
source-level completion rather than a fuel or return-code failure. -/
theorem collapse_succeeded
    {reverse : Bool} {inputSize : Nat}
    {openState : MergeState κ ν}
    {collapsed : MergeForceCollapseResult κ ν}
    {execution : TraceResult (ListSortImplResult κ ν)}
    (reached :
      ListSortScanReachedCollapse reverse inputSize openState collapsed
        execution) :
    collapsed.returnCode = 0 ∧ collapsed.fuelExhausted = false := by
  induction reached with
  | terminal _ _ _ hcode hfuel => exact ⟨hcode, hfuel⟩
  | bindPrefix _ _ _ _ _ ih => exact ih
  | prependMemoryEvent _ _ _ ih => exact ih

end ListSortScanReachedCollapse

end CPythonListsort
