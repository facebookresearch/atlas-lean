/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Transcription.MergeMemory

/-!
# Compositional access and pending-push traces

This module provides the trace carrier used by the comparator-independent
safety layer.  An access event describes an *attempt*: instrumentation emits
the event before consulting the modeled array, so an invalid access is retained
in the trace even when the local evaluator returns `none`.  Temporary payload
events carry the backing state observed at that same point.  Reads of
`TempStorage.hasValues` and `MergeState.alloced` are metadata reads, not payload
events, and therefore do not use the temporary-payload region.

Local instrumented evaluators return `TraceResult`s.  `TraceResult.bind`
concatenates their local traces in execution order and preserves the trace of a
failed operation.  The later top-level instrumented evaluator must be assembled
from those local evaluators; wrapping the existing evaluator in an empty trace
would not satisfy this interface's intended use.

Pending pushes are deliberately separate from ordinary indexed accesses.  The
wrapper below performs the existing unconditional `Array.push` first and then
records its resulting depth.  There is no capacity guard, refusal result,
clamping operation, or assertion-failure event in this trace model.
-/

namespace CPythonListsort

universe u v w

/-- Whether an ordinary indexed access attempts to read or write its region. -/
inductive AccessKind where
  | read
  | write
  deriving DecidableEq, Repr

/-- The array-like region addressed by an ordinary access attempt.

The backing constructor argument is observed at the temporary payload access
itself.  Encoding it in the region prevents a temporary event from silently
omitting the backing state.  Pending-stack `Array.push` is not a
`pendingRuns` access; only indexed reads and writes use that constructor. -/
inductive AccessRegion where
  | inputKeys
  | synchronizedValues
  | tempPayload (backingAtAttempt : TempBacking)
  | pendingRuns
  deriving DecidableEq, Repr

/-- One ordinary indexed access attempt.  Signed indices are retained so a
negative rejected attempt is represented faithfully rather than coerced to a
natural number.  `extent` is the region's length at the time of the attempt. -/
structure AccessEvent where
  kind : AccessKind
  region : AccessRegion
  index : Int
  extent : Nat
  deriving DecidableEq, Repr

namespace AccessEvent

/-- The attempted signed index lies in the half-open interval `[0, extent)`. -/
def InBounds (event : AccessEvent) : Prop :=
  0 ≤ event.index ∧ event.index < Int.ofNat event.extent

instance (event : AccessEvent) : Decidable event.InBounds :=
  inferInstanceAs (Decidable (0 ≤ event.index ∧ event.index < Int.ofNat event.extent))

/-- A temporary payload attempt observes live rather than released backing.
Non-temporary events satisfy this predicate vacuously. -/
def TempPayloadLive (event : AccessEvent) : Prop :=
  match event.region with
  | .tempPayload backing => backing ≠ .released
  | _ => True

instance (event : AccessEvent) : Decidable event.TempPayloadLive := by
  unfold TempPayloadLive
  split <;> infer_instance

end AccessEvent

/-! ## Type-erased merge-memory history -/

/-- The storage facts retained at one merge-memory boundary.

The snapshot deliberately contains only decidable, type-erased observations.
`mainValuePresent` records, in main-array order, whether each entry carries a
synchronized value.  It records the raw state rather than a Boolean claiming
that any storage invariant holds; later safety modules must validate the
snapshot independently. -/
structure MergeMemorySnapshot where
  backing : TempBacking
  hasValues : Bool
  cellsSize : Nat
  alloced : PySSize
  physicalSlots : Nat
  mainValuePresent : List Bool
  deriving DecidableEq, Repr

namespace MergeMemorySnapshot

/-- Extensionality for the type-erased storage observation. -/
@[ext]
theorem ext {left right : MergeMemorySnapshot}
    (backing : left.backing = right.backing)
    (hasValues : left.hasValues = right.hasValues)
    (cellsSize : left.cellsSize = right.cellsSize)
    (alloced : left.alloced = right.alloced)
    (physicalSlots : left.physicalSlots = right.physicalSlots)
    (mainValuePresent : left.mainValuePresent = right.mainValuePresent) :
    left = right := by
  cases left
  cases right
  simp_all

/-- Type-erase exactly the merge-memory observations present in `state`. -/
def ofState (state : MergeState κ ν) : MergeMemorySnapshot :=
  { backing := state.a.backing
    hasValues := state.a.hasValues
    cellsSize := state.a.cells.size
    alloced := state.alloced
    physicalSlots := state.a.physicalSlots
    mainValuePresent :=
      state.data.entries.toList.map fun entry => entry.value.isSome }

end MergeMemorySnapshot

/-- Which directional merge consumed one `merge_getmem` result. -/
inductive MergeMemoryDirection where
  | lo
  | hi
  deriving DecidableEq, Repr

/-- Raw observations spanning one directional merge call.

`sourceLeftLength` and `sourceRightLength` retain the two run lengths before
`merge_at` trimming; `na` and `nb` are the lengths actually passed to the
directional merge.  `intermediateFree` is an observation slot, not a claim:
the later safety layer must prove when it is `none`, when it is `some`, and
that any supplied snapshot is the state immediately after `merge_freemem`.
Likewise, this record does not assert that `request`, `outcome`, or any of the
snapshots agree with the modeled transition. -/
structure MergeMemoryCallEvent where
  direction : MergeMemoryDirection
  request : PySSize
  na : Nat
  nb : Nat
  sourceLeftLength : PySSize
  sourceRightLength : PySSize
  listlen : PySSize
  outcome : MergeGetmemOutcome
  before : MergeMemorySnapshot
  intermediateFree : Option MergeMemorySnapshot
  afterGetmem : MergeMemorySnapshot
  afterMerge : MergeMemorySnapshot
  deriving DecidableEq, Repr

/-- Chronological merge-memory boundary observations.

These constructors are intentionally non-validating.  They retain enough raw
data for a separate lifecycle predicate to compare the snapshots with
`merge_init`, `merge_getmem`, the directional merge, and `merge_freemem`
without making any of those obligations true by construction. -/
inductive MergeMemoryEvent where
  | initial (state : MergeMemorySnapshot)
  | mergeCall (call : MergeMemoryCallEvent)
  | cleanup (before after : MergeMemorySnapshot)
  deriving DecidableEq, Repr

/-! ## Type-erased policy history -/

/-- The source interval occupied by one pending run.

This is a raw, type-erased observation.  In particular, the structure itself
does not assert positivity, adjacency, or containment in the input. -/
structure RunSpan where
  base : Nat
  len : Nat
  deriving DecidableEq, Repr

namespace RunSpan

/-- Forget the pending run's power and retain its source interval. -/
def ofPendingRun (run : PendingRun) : RunSpan :=
  { base := run.base, len := run.len.toNat }

end RunSpan

/-- Raw observations attached to the successful push of one formed run.

`naturalLength` is the length returned by run discovery, `target` is the
current adaptive-minrun target, and `remainingBefore` is the unscanned length
before this run is consumed.  Keeping all three separate makes both the
extended-short-run and already-long-natural-run cases observable. -/
structure PendingPushEvent where
  run : RunSpan
  depthAfter : Nat
  naturalLength : Nat
  target : Nat
  remainingBefore : Nat
  deriving DecidableEq, Repr

/-- One logical merge, recorded at the successful pending-stack splice.

The two operands are the full pre-trimming pending runs.  Consequently, this
event remains present when galloping later discovers that no directional data
movement is needed. -/
structure LogicalMergeEvent where
  index : Nat
  left : RunSpan
  right : RunSpan
  deriving DecidableEq, Repr

/-- Policy-level events needed to reconstruct formed leaves and logical merge
nodes independently of physical access and merge-memory traces. -/
inductive PolicyEvent where
  | formed (push : PendingPushEvent)
  | merge (event : LogicalMergeEvent)
  deriving DecidableEq, Repr

/-- Ordered observations made by an instrumented evaluator.

`accesses`, `pushDepths`, `memoryEvents`, and `policyEvents` are chronological
within their respective channels.  A `pushDepths` entry is the pending-array
size *after* one unconditional push.  Fuel exhaustion composes by Boolean
disjunction. -/
structure AccessTrace where
  accesses : List AccessEvent
  pushDepths : List Nat
  memoryEvents : List MergeMemoryEvent := []
  policyEvents : List PolicyEvent := []
  fuelExhausted : Bool
  deriving DecidableEq, Repr

namespace AccessTrace

/-- The trace containing no observations. -/
def empty : AccessTrace :=
  { accesses := []
    pushDepths := []
    memoryEvents := []
    policyEvents := []
    fuelExhausted := false }

/-- Sequential trace composition, with the left trace occurring first. -/
def compose (earlier later : AccessTrace) : AccessTrace :=
  { accesses := earlier.accesses ++ later.accesses
    pushDepths := earlier.pushDepths ++ later.pushDepths
    memoryEvents := earlier.memoryEvents ++ later.memoryEvents
    policyEvents := earlier.policyEvents ++ later.policyEvents
    fuelExhausted := earlier.fuelExhausted || later.fuelExhausted }

/-- Low-level constructor for one access-attempt trace.  It intentionally
accepts an explicit region and extent so the typed wrappers later in this file
can share one implementation.  Instrumented listsort code should use those
state-derived wrappers instead of manufacturing labels or extents itself.  No
bounds or liveness filter is applied: rejected attempts remain observable. -/
def singletonAccess (kind : AccessKind) (region : AccessRegion)
    (index : Int) (extent : Nat) : AccessTrace :=
  { accesses := [{ kind := kind, region := region, index := index, extent := extent }]
    pushDepths := []
    memoryEvents := []
    policyEvents := []
    fuelExhausted := false }

/-- The local trace emitted after one pending-stack push. -/
def singletonPushDepth (depth : Nat) : AccessTrace :=
  { accesses := []
    pushDepths := [depth]
    memoryEvents := []
    policyEvents := []
    fuelExhausted := false }

/-- The local trace containing one raw merge-memory boundary observation. -/
def singletonMemoryEvent (event : MergeMemoryEvent) : AccessTrace :=
  { accesses := []
    pushDepths := []
    memoryEvents := [event]
    policyEvents := []
    fuelExhausted := false }

/-- The local trace containing one raw policy observation. -/
def singletonPolicyEvent (event : PolicyEvent) : AccessTrace :=
  { accesses := []
    pushDepths := []
    memoryEvents := []
    policyEvents := [event]
    fuelExhausted := false }

/-- The aligned depth and policy observations emitted by a formed-run push. -/
def singletonFormedRun (event : PendingPushEvent) : AccessTrace :=
  { accesses := []
    pushDepths := [event.depthAfter]
    memoryEvents := []
    policyEvents := [.formed event]
    fuelExhausted := false }

/-- A local evaluator exhausted one of its explicit fuel counters. -/
def exhausted : AccessTrace :=
  { accesses := []
    pushDepths := []
    memoryEvents := []
    policyEvents := []
    fuelExhausted := true }

/-- Every ordinary access attempt is within the extent recorded beside it. -/
def allAccessesInBounds (trace : AccessTrace) : Prop :=
  ∀ event ∈ trace.accesses, event.InBounds

instance (trace : AccessTrace) : Decidable trace.allAccessesInBounds :=
  inferInstanceAs (Decidable (∀ event ∈ trace.accesses, event.InBounds))

/-- No temporary payload access attempt observed released backing.

Because this quantifies over all recorded attempts, an out-of-bounds temporary
attempt is not filtered out before the storage-liveness check. -/
def tempPayloadAccessesLive (trace : AccessTrace) : Prop :=
  ∀ event ∈ trace.accesses, event.TempPayloadLive

instance (trace : AccessTrace) : Decidable trace.tempPayloadAccessesLive :=
  inferInstanceAs (Decidable (∀ event ∈ trace.accesses, event.TempPayloadLive))

/-- Maximum recorded post-push depth, with zero for a trace with no pushes. -/
def stackDepthMax (trace : AccessTrace) : Nat :=
  trace.pushDepths.foldl Nat.max 0

@[simp]
theorem compose_empty_left (trace : AccessTrace) : compose empty trace = trace := by
  cases trace
  simp [compose, empty]

@[simp]
theorem compose_empty_right (trace : AccessTrace) : compose trace empty = trace := by
  cases trace
  simp [compose, empty]

theorem compose_assoc (first second third : AccessTrace) :
    compose (compose first second) third = compose first (compose second third) := by
  cases first
  cases second
  cases third
  simp [compose, List.append_assoc, Bool.or_assoc]

@[simp]
theorem fuelExhausted_compose (earlier later : AccessTrace) :
    (compose earlier later).fuelExhausted =
      (earlier.fuelExhausted || later.fuelExhausted) := by
  rfl

@[simp]
theorem policyEvents_compose (earlier later : AccessTrace) :
    (compose earlier later).policyEvents =
      earlier.policyEvents ++ later.policyEvents := by
  rfl

@[simp]
theorem policyEvents_empty : empty.policyEvents = [] := by
  rfl

@[simp]
theorem policyEvents_singletonPolicyEvent (event : PolicyEvent) :
    (singletonPolicyEvent event).policyEvents = [event] := by
  rfl

@[simp]
theorem policyEvents_singletonFormedRun (event : PendingPushEvent) :
    (singletonFormedRun event).policyEvents = [.formed event] := by
  rfl

@[simp]
theorem fuelExhausted_compose_eq_false (earlier later : AccessTrace) :
    (compose earlier later).fuelExhausted = false ↔
      earlier.fuelExhausted = false ∧ later.fuelExhausted = false := by
  cases hEarlier : earlier.fuelExhausted <;>
    cases hLater : later.fuelExhausted <;>
    simp [compose, hEarlier, hLater]

@[simp]
theorem allAccessesInBounds_empty : empty.allAccessesInBounds := by
  simp [allAccessesInBounds, empty]

@[simp]
theorem allAccessesInBounds_compose (earlier later : AccessTrace) :
    (compose earlier later).allAccessesInBounds ↔
      earlier.allAccessesInBounds ∧ later.allAccessesInBounds := by
  simp only [allAccessesInBounds, compose, List.mem_append]
  aesop

@[simp]
theorem tempPayloadAccessesLive_empty : empty.tempPayloadAccessesLive := by
  simp [tempPayloadAccessesLive, empty]

@[simp]
theorem tempPayloadAccessesLive_compose (earlier later : AccessTrace) :
    (compose earlier later).tempPayloadAccessesLive ↔
      earlier.tempPayloadAccessesLive ∧ later.tempPayloadAccessesLive := by
  simp only [tempPayloadAccessesLive, compose, List.mem_append]
  aesop

@[simp]
theorem stackDepthMax_empty : empty.stackDepthMax = 0 := by
  rfl

@[simp]
theorem stackDepthMax_singletonPushDepth (depth : Nat) :
    (singletonPushDepth depth).stackDepthMax = depth := by
  simp [stackDepthMax, singletonPushDepth]

@[simp]
theorem stackDepthMax_singletonFormedRun (event : PendingPushEvent) :
    (singletonFormedRun event).stackDepthMax = event.depthAfter := by
  simp [stackDepthMax, singletonFormedRun]

private theorem foldl_max_eq_max_foldl_zero (depths : List Nat) (initial : Nat) :
    depths.foldl Nat.max initial =
      Nat.max initial (depths.foldl Nat.max 0) := by
  induction depths generalizing initial with
  | nil => simp
  | cons depth depths ih =>
      simp only [List.foldl_cons]
      rw [ih (Nat.max initial depth), ih (Nat.max 0 depth)]
      have hZero : Nat.max 0 depth = depth := Nat.max_eq_right (Nat.zero_le depth)
      rw [hZero]
      ac_rfl

/-- Sequential composition takes the exact maximum of the component push
depths; in particular, composing with an access-only trace cannot alter it. -/
@[simp]
theorem stackDepthMax_compose (earlier later : AccessTrace) :
    (compose earlier later).stackDepthMax =
      Nat.max earlier.stackDepthMax later.stackDepthMax := by
  simp only [stackDepthMax, compose, List.foldl_append]
  exact foldl_max_eq_max_foldl_zero later.pushDepths
    (earlier.pushDepths.foldl Nat.max 0)

end AccessTrace

/-- The result type used by local instrumented evaluators.

An invalid modeled operation returns `none`, but its already-produced trace is
retained.  Successful continuations compose their observations in order. -/
structure TraceResult (α : Type u) where
  result : Option α
  trace : AccessTrace
  deriving DecidableEq, Repr

namespace TraceResult

/-- Forget instrumentation and recover the underlying partial result. -/
def erase (current : TraceResult α) : Option α :=
  current.result

/-- A successful operation with no local observations. -/
def pure (value : α) : TraceResult α :=
  { result := some value, trace := AccessTrace.empty }

/-- A failed operation with no local observations.  Accessing evaluators should
instead use `captureAccess` so the rejected attempt is not erased. -/
def failure : TraceResult α :=
  { result := none, trace := AccessTrace.empty }

/-- Short-circuiting sequential composition for local instrumented evaluators. -/
def bind (current : TraceResult α) (next : α → TraceResult β) : TraceResult β :=
  match current.result with
  | none => { result := none, trace := current.trace }
  | some value =>
      let following := next value
      { result := following.result
        trace := current.trace.compose following.trace }

/-- Transform a successful local result without changing its observations. -/
def map (current : TraceResult α) (transform : α → β) : TraceResult β :=
  { result := current.result.map transform
    trace := current.trace }

/-- Record one merge-memory boundary before all observations already present
in `current`.  This operation never changes success or failure. -/
def prependMemoryEvent (current : TraceResult α)
    (event : MergeMemoryEvent) : TraceResult α :=
  { result := current.result
    trace := (AccessTrace.singletonMemoryEvent event).compose current.trace }

/-- Record one merge-memory boundary after all observations already present
in `current`.  This operation never changes success or failure. -/
def appendMemoryEvent (current : TraceResult α)
    (event : MergeMemoryEvent) : TraceResult α :=
  { result := current.result
    trace := current.trace.compose (AccessTrace.singletonMemoryEvent event) }

/-- Append a boundary observation exactly when the modeled operation
succeeds.  A failed operation retains its existing trace and does not invent
a completed transition.  The event is computed from the actual successful
result, rather than from a separately supplied witness. -/
def recordSuccessMemoryEvent (current : TraceResult α)
    (event : α → MergeMemoryEvent) : TraceResult α :=
  match current.result with
  | none => current
  | some value => current.appendMemoryEvent (event value)

/-- Record one policy event after all observations already present in
`current`.  This operation never changes success or failure. -/
def appendPolicyEvent (current : TraceResult α)
    (event : PolicyEvent) : TraceResult α :=
  { result := current.result
    trace := current.trace.compose (AccessTrace.singletonPolicyEvent event) }

/-- Append a policy event exactly when the modeled operation succeeds.

A failed operation retains its attempted lower-level accesses but does not
invent a completed logical transition.  Computing the event from the returned
value also permits future callers to retain result-dependent observations. -/
def recordSuccessPolicyEvent (current : TraceResult α)
    (event : α → PolicyEvent) : TraceResult α :=
  match current.result with
  | none => current
  | some value => current.appendPolicyEvent (event value)

@[simp]
theorem erase_pure (value : α) : (pure value).erase = some value := by
  rfl

@[simp]
theorem erase_failure : (failure : TraceResult α).erase = none := by
  rfl

@[simp]
theorem erase_map (transform : α → β) (current : TraceResult α) :
    (current.map transform).erase = current.erase.map transform := by
  rfl

@[simp]
theorem result_prependMemoryEvent (current : TraceResult α)
    (event : MergeMemoryEvent) :
    (current.prependMemoryEvent event).result = current.result := by
  rfl

@[simp]
theorem result_appendMemoryEvent (current : TraceResult α)
    (event : MergeMemoryEvent) :
    (current.appendMemoryEvent event).result = current.result := by
  rfl

@[simp]
theorem erase_prependMemoryEvent (current : TraceResult α)
    (event : MergeMemoryEvent) :
    (current.prependMemoryEvent event).erase = current.erase := by
  rfl

@[simp]
theorem erase_appendMemoryEvent (current : TraceResult α)
    (event : MergeMemoryEvent) :
    (current.appendMemoryEvent event).erase = current.erase := by
  rfl

@[simp]
theorem result_recordSuccessMemoryEvent (current : TraceResult α)
    (event : α → MergeMemoryEvent) :
    (current.recordSuccessMemoryEvent event).result = current.result := by
  cases hresult : current.result <;>
    simp [recordSuccessMemoryEvent, hresult]

@[simp]
theorem erase_recordSuccessMemoryEvent (current : TraceResult α)
    (event : α → MergeMemoryEvent) :
    (current.recordSuccessMemoryEvent event).erase = current.erase := by
  simp [TraceResult.erase]

@[simp]
theorem result_appendPolicyEvent (current : TraceResult α)
    (event : PolicyEvent) :
    (current.appendPolicyEvent event).result = current.result := by
  rfl

@[simp]
theorem erase_appendPolicyEvent (current : TraceResult α)
    (event : PolicyEvent) :
    (current.appendPolicyEvent event).erase = current.erase := by
  rfl

@[simp]
theorem result_recordSuccessPolicyEvent (current : TraceResult α)
    (event : α → PolicyEvent) :
    (current.recordSuccessPolicyEvent event).result = current.result := by
  cases hresult : current.result <;>
    simp [recordSuccessPolicyEvent, hresult]

@[simp]
theorem erase_recordSuccessPolicyEvent (current : TraceResult α)
    (event : α → PolicyEvent) :
    (current.recordSuccessPolicyEvent event).erase = current.erase := by
  simp [TraceResult.erase]

@[simp]
theorem accesses_prependMemoryEvent (current : TraceResult α)
    (event : MergeMemoryEvent) :
    (current.prependMemoryEvent event).trace.accesses = current.trace.accesses := by
  rfl

@[simp]
theorem accesses_appendMemoryEvent (current : TraceResult α)
    (event : MergeMemoryEvent) :
    (current.appendMemoryEvent event).trace.accesses = current.trace.accesses := by
  simp [appendMemoryEvent, AccessTrace.compose,
    AccessTrace.singletonMemoryEvent]

@[simp]
theorem pushDepths_prependMemoryEvent (current : TraceResult α)
    (event : MergeMemoryEvent) :
    (current.prependMemoryEvent event).trace.pushDepths =
      current.trace.pushDepths := by
  rfl

@[simp]
theorem pushDepths_appendMemoryEvent (current : TraceResult α)
    (event : MergeMemoryEvent) :
    (current.appendMemoryEvent event).trace.pushDepths =
      current.trace.pushDepths := by
  simp [appendMemoryEvent, AccessTrace.compose,
    AccessTrace.singletonMemoryEvent]

@[simp]
theorem memoryEvents_prependMemoryEvent (current : TraceResult α)
    (event : MergeMemoryEvent) :
    (current.prependMemoryEvent event).trace.memoryEvents =
      event :: current.trace.memoryEvents := by
  rfl

@[simp]
theorem memoryEvents_appendMemoryEvent (current : TraceResult α)
    (event : MergeMemoryEvent) :
    (current.appendMemoryEvent event).trace.memoryEvents =
      current.trace.memoryEvents ++ [event] := by
  rfl

theorem memoryEvents_recordSuccessMemoryEvent_of_eq_some
    (current : TraceResult α) (event : α → MergeMemoryEvent)
    (value : α) (hresult : current.result = some value) :
    (current.recordSuccessMemoryEvent event).trace.memoryEvents =
      current.trace.memoryEvents ++ [event value] := by
  simp [recordSuccessMemoryEvent, hresult]

@[simp]
theorem policyEvents_prependMemoryEvent (current : TraceResult α)
    (event : MergeMemoryEvent) :
    (current.prependMemoryEvent event).trace.policyEvents =
      current.trace.policyEvents := by
  rfl

@[simp]
theorem policyEvents_appendMemoryEvent (current : TraceResult α)
    (event : MergeMemoryEvent) :
    (current.appendMemoryEvent event).trace.policyEvents =
      current.trace.policyEvents := by
  simp [appendMemoryEvent, AccessTrace.compose,
    AccessTrace.singletonMemoryEvent]

@[simp]
theorem policyEvents_recordSuccessMemoryEvent (current : TraceResult α)
    (event : α → MergeMemoryEvent) :
    (current.recordSuccessMemoryEvent event).trace.policyEvents =
      current.trace.policyEvents := by
  cases hresult : current.result <;>
    simp [recordSuccessMemoryEvent, hresult]

@[simp]
theorem policyEvents_appendPolicyEvent (current : TraceResult α)
    (event : PolicyEvent) :
    (current.appendPolicyEvent event).trace.policyEvents =
      current.trace.policyEvents ++ [event] := by
  rfl

theorem policyEvents_recordSuccessPolicyEvent_of_eq_some
    (current : TraceResult α) (event : α → PolicyEvent)
    (value : α) (hresult : current.result = some value) :
    (current.recordSuccessPolicyEvent event).trace.policyEvents =
      current.trace.policyEvents ++ [event value] := by
  simp [recordSuccessPolicyEvent, hresult]

theorem policyEvents_recordSuccessPolicyEvent_of_eq_none
    (current : TraceResult α) (event : α → PolicyEvent)
    (hresult : current.result = none) :
    (current.recordSuccessPolicyEvent event).trace.policyEvents =
      current.trace.policyEvents := by
  simp [recordSuccessPolicyEvent, hresult]

@[simp]
theorem fuelExhausted_prependMemoryEvent (current : TraceResult α)
    (event : MergeMemoryEvent) :
    (current.prependMemoryEvent event).trace.fuelExhausted =
      current.trace.fuelExhausted := by
  rfl

@[simp]
theorem fuelExhausted_appendMemoryEvent (current : TraceResult α)
    (event : MergeMemoryEvent) :
    (current.appendMemoryEvent event).trace.fuelExhausted =
      current.trace.fuelExhausted := by
  simp [appendMemoryEvent, AccessTrace.compose,
    AccessTrace.singletonMemoryEvent]

@[simp]
theorem accesses_recordSuccessMemoryEvent (current : TraceResult α)
    (event : α → MergeMemoryEvent) :
    (current.recordSuccessMemoryEvent event).trace.accesses =
      current.trace.accesses := by
  cases hresult : current.result <;>
    simp [recordSuccessMemoryEvent, hresult]

@[simp]
theorem pushDepths_recordSuccessMemoryEvent (current : TraceResult α)
    (event : α → MergeMemoryEvent) :
    (current.recordSuccessMemoryEvent event).trace.pushDepths =
      current.trace.pushDepths := by
  cases hresult : current.result <;>
    simp [recordSuccessMemoryEvent, hresult]

@[simp]
theorem fuelExhausted_recordSuccessMemoryEvent (current : TraceResult α)
    (event : α → MergeMemoryEvent) :
    (current.recordSuccessMemoryEvent event).trace.fuelExhausted =
      current.trace.fuelExhausted := by
  cases hresult : current.result <;>
    simp [recordSuccessMemoryEvent, hresult]

@[simp]
theorem allAccessesInBounds_recordSuccessMemoryEvent
    (current : TraceResult α) (event : α → MergeMemoryEvent) :
    (current.recordSuccessMemoryEvent event).trace.allAccessesInBounds ↔
      current.trace.allAccessesInBounds := by
  simp [AccessTrace.allAccessesInBounds]

@[simp]
theorem tempPayloadAccessesLive_recordSuccessMemoryEvent
    (current : TraceResult α) (event : α → MergeMemoryEvent) :
    (current.recordSuccessMemoryEvent event).trace.tempPayloadAccessesLive ↔
      current.trace.tempPayloadAccessesLive := by
  simp [AccessTrace.tempPayloadAccessesLive]

@[simp]
theorem stackDepthMax_prependMemoryEvent (current : TraceResult α)
    (event : MergeMemoryEvent) :
    (current.prependMemoryEvent event).trace.stackDepthMax =
      current.trace.stackDepthMax := by
  simp only [prependMemoryEvent, AccessTrace.stackDepthMax,
    AccessTrace.compose, AccessTrace.singletonMemoryEvent, List.nil_append]

@[simp]
theorem stackDepthMax_appendMemoryEvent (current : TraceResult α)
    (event : MergeMemoryEvent) :
    (current.appendMemoryEvent event).trace.stackDepthMax =
      current.trace.stackDepthMax := by
  simp only [appendMemoryEvent, AccessTrace.stackDepthMax,
    AccessTrace.compose, AccessTrace.singletonMemoryEvent, List.append_nil]

@[simp]
theorem stackDepthMax_recordSuccessMemoryEvent (current : TraceResult α)
    (event : α → MergeMemoryEvent) :
    (current.recordSuccessMemoryEvent event).trace.stackDepthMax =
      current.trace.stackDepthMax := by
  cases hresult : current.result <;>
    simp [recordSuccessMemoryEvent, hresult]

@[simp]
theorem accesses_appendPolicyEvent (current : TraceResult α)
    (event : PolicyEvent) :
    (current.appendPolicyEvent event).trace.accesses =
      current.trace.accesses := by
  simp [appendPolicyEvent, AccessTrace.compose,
    AccessTrace.singletonPolicyEvent]

@[simp]
theorem pushDepths_appendPolicyEvent (current : TraceResult α)
    (event : PolicyEvent) :
    (current.appendPolicyEvent event).trace.pushDepths =
      current.trace.pushDepths := by
  simp [appendPolicyEvent, AccessTrace.compose,
    AccessTrace.singletonPolicyEvent]

@[simp]
theorem memoryEvents_appendPolicyEvent (current : TraceResult α)
    (event : PolicyEvent) :
    (current.appendPolicyEvent event).trace.memoryEvents =
      current.trace.memoryEvents := by
  simp [appendPolicyEvent, AccessTrace.compose,
    AccessTrace.singletonPolicyEvent]

@[simp]
theorem fuelExhausted_appendPolicyEvent (current : TraceResult α)
    (event : PolicyEvent) :
    (current.appendPolicyEvent event).trace.fuelExhausted =
      current.trace.fuelExhausted := by
  simp [appendPolicyEvent, AccessTrace.compose,
    AccessTrace.singletonPolicyEvent]

@[simp]
theorem accesses_recordSuccessPolicyEvent (current : TraceResult α)
    (event : α → PolicyEvent) :
    (current.recordSuccessPolicyEvent event).trace.accesses =
      current.trace.accesses := by
  cases hresult : current.result <;>
    simp [recordSuccessPolicyEvent, hresult]

@[simp]
theorem pushDepths_recordSuccessPolicyEvent (current : TraceResult α)
    (event : α → PolicyEvent) :
    (current.recordSuccessPolicyEvent event).trace.pushDepths =
      current.trace.pushDepths := by
  cases hresult : current.result <;>
    simp [recordSuccessPolicyEvent, hresult]

@[simp]
theorem memoryEvents_recordSuccessPolicyEvent (current : TraceResult α)
    (event : α → PolicyEvent) :
    (current.recordSuccessPolicyEvent event).trace.memoryEvents =
      current.trace.memoryEvents := by
  cases hresult : current.result <;>
    simp [recordSuccessPolicyEvent, hresult]

@[simp]
theorem fuelExhausted_recordSuccessPolicyEvent (current : TraceResult α)
    (event : α → PolicyEvent) :
    (current.recordSuccessPolicyEvent event).trace.fuelExhausted =
      current.trace.fuelExhausted := by
  cases hresult : current.result <;>
    simp [recordSuccessPolicyEvent, hresult]

@[simp]
theorem allAccessesInBounds_recordSuccessPolicyEvent
    (current : TraceResult α) (event : α → PolicyEvent) :
    (current.recordSuccessPolicyEvent event).trace.allAccessesInBounds ↔
      current.trace.allAccessesInBounds := by
  simp [AccessTrace.allAccessesInBounds]

@[simp]
theorem tempPayloadAccessesLive_recordSuccessPolicyEvent
    (current : TraceResult α) (event : α → PolicyEvent) :
    (current.recordSuccessPolicyEvent event).trace.tempPayloadAccessesLive ↔
      current.trace.tempPayloadAccessesLive := by
  simp [AccessTrace.tempPayloadAccessesLive]

@[simp]
theorem stackDepthMax_appendPolicyEvent (current : TraceResult α)
    (event : PolicyEvent) :
    (current.appendPolicyEvent event).trace.stackDepthMax =
      current.trace.stackDepthMax := by
  simp only [appendPolicyEvent, AccessTrace.stackDepthMax,
    AccessTrace.compose, AccessTrace.singletonPolicyEvent, List.append_nil]

@[simp]
theorem stackDepthMax_recordSuccessPolicyEvent (current : TraceResult α)
    (event : α → PolicyEvent) :
    (current.recordSuccessPolicyEvent event).trace.stackDepthMax =
      current.trace.stackDepthMax := by
  cases hresult : current.result <;>
    simp [recordSuccessPolicyEvent, hresult]

/-- Erasing a composed instrumented computation gives exactly ordinary
`Option.bind`; tracing neither creates successes nor hides failures. -/
@[simp]
theorem erase_bind (current : TraceResult α) (next : α → TraceResult β) :
    (current.bind next).erase =
      current.erase.bind (fun value => (next value).erase) := by
  cases current with
  | mk result trace =>
      cases result <;> rfl

/-- The trace side of `bind`: a rejected first operation retains its local
trace, while a successful continuation appends its trace in execution order. -/
theorem trace_bind (current : TraceResult α) (next : α → TraceResult β) :
    (current.bind next).trace =
      match current.result with
      | none => current.trace
      | some value => current.trace.compose (next value).trace := by
  cases current with
  | mk result trace =>
      cases result <;> rfl

/-- Event-freedom composes through a bind.  This is the common structural
lemma used to pin that lower-level access helpers cannot manufacture a
top-level merge-memory boundary. -/
theorem memoryEvents_bind_eq_nil (current : TraceResult α)
    (next : α → TraceResult β)
    (hcurrent : current.trace.memoryEvents = [])
    (hnext : ∀ value, (next value).trace.memoryEvents = []) :
    (current.bind next).trace.memoryEvents = [] := by
  rw [trace_bind]
  cases hresult : current.result with
  | none => exact hcurrent
  | some value =>
      simp [AccessTrace.compose, hcurrent, hnext value]

/-- Policy-event freedom composes through a bind. -/
theorem policyEvents_bind_eq_nil (current : TraceResult α)
    (next : α → TraceResult β)
    (hcurrent : current.trace.policyEvents = [])
    (hnext : ∀ value, (next value).trace.policyEvents = []) :
    (current.bind next).trace.policyEvents = [] := by
  rw [trace_bind]
  cases hresult : current.result with
  | none => exact hcurrent
  | some value =>
      simp [AccessTrace.compose, hcurrent, hnext value]

@[simp]
theorem memoryEvents_map (current : TraceResult α) (transform : α → β) :
    (current.map transform).trace.memoryEvents = current.trace.memoryEvents := by
  rfl

@[simp]
theorem policyEvents_map (current : TraceResult α) (transform : α → β) :
    (current.map transform).trace.policyEvents = current.trace.policyEvents := by
  rfl

/-- The policy-history side of `bind`, stated independently of the other trace
channels so consumers do not need to unfold the trace carrier. -/
theorem policyEvents_bind (current : TraceResult α)
    (next : α → TraceResult β) :
    (current.bind next).trace.policyEvents =
      match current.result with
      | none => current.trace.policyEvents
      | some value => current.trace.policyEvents ++
          (next value).trace.policyEvents := by
  rw [trace_bind]
  cases current.result <;> rfl

/-- Low-level attachment of one access-attempt event to an already-computed
modeled result.  The event is present whether `result` is `some` or `none`.
Callers should normally use one of the state-derived access wrappers below. -/
def captureAccess (kind : AccessKind) (region : AccessRegion)
    (index : Int) (extent : Nat) (result : Option α) : TraceResult α :=
  { result := result
    trace := AccessTrace.singletonAccess kind region index extent }

/-- Low-level array-read instrumenter shared by the region-specific wrappers.
Negative and past-the-end attempts return `none` only after their event has
been formed.  Callers should not supply ad-hoc labels for listsort storage. -/
def arrayRead? (region : AccessRegion) (array : Array α)
    (index : Int) : TraceResult α :=
  let result :=
    if 0 ≤ index then
      array[index.toNat]?
    else
      none
  captureAccess .read region index array.size result

/-- Low-level array-write instrumenter shared by the region-specific wrappers.
Rejected writes leave the source array untouched by returning `none`, while
retaining the event.  Callers should not supply ad-hoc labels for listsort
storage. -/
def arrayWrite? (region : AccessRegion) (array : Array α)
    (index : Int) (value : α) : TraceResult (Array α) :=
  let result :=
    if 0 ≤ index ∧ index.toNat < array.size then
      some (array.setIfInBounds index.toNat value)
    else
      none
  captureAccess .write region index array.size result

/-- Mark a local result as fuel-exhausted without disturbing prior events. -/
def markFuelExhausted (current : TraceResult α) : TraceResult α :=
  { current with trace := current.trace.compose AccessTrace.exhausted }

@[simp]
theorem erase_markFuelExhausted (current : TraceResult α) :
    current.markFuelExhausted.erase = current.erase := by
  rfl

@[simp]
theorem trace_captureAccess (kind : AccessKind) (region : AccessRegion)
    (index : Int) (extent : Nat) (result : Option α) :
    (captureAccess kind region index extent result).trace =
      AccessTrace.singletonAccess kind region index extent := by
  rfl

@[simp]
theorem trace_arrayRead (region : AccessRegion) (array : Array α)
    (index : Int) :
    (arrayRead? region array index).trace =
      AccessTrace.singletonAccess .read region index array.size := by
  rfl

@[simp]
theorem trace_arrayWrite (region : AccessRegion) (array : Array α)
    (index : Int) (value : α) :
    (arrayWrite? region array index value).trace =
      AccessTrace.singletonAccess .write region index array.size := by
  rfl

@[simp]
theorem erase_captureAccess (kind : AccessKind) (region : AccessRegion)
    (index : Int) (extent : Nat) (result : Option α) :
    (captureAccess kind region index extent result).erase = result := by
  rfl

@[simp]
theorem erase_arrayRead (region : AccessRegion) (array : Array α)
    (index : Int) :
    (arrayRead? region array index).erase =
      if 0 ≤ index then array[index.toNat]? else none := by
  rfl

@[simp]
theorem erase_arrayWrite (region : AccessRegion) (array : Array α)
    (index : Int) (value : α) :
    (arrayWrite? region array index value).erase =
      if 0 ≤ index ∧ index.toNat < array.size then
        some (array.setIfInBounds index.toNat value)
      else
        none := by
  rfl

end TraceResult

/-! ## State-derived access wrappers -/

namespace TraceResult

/-- Read one initialized temporary payload cell.  Both the region's backing
and its extent come from `storage` at the attempt.  An in-bounds but
uninitialized (`none`) cell rejects the read only after preserving that event. -/
def tempPayloadRead? (storage : TempStorage κ ν) (index : Int) :
    TraceResult (SortSliceEntry κ ν) :=
  (arrayRead? (.tempPayload storage.backing) storage.cells index).bind fun cell =>
    match cell with
    | none => failure
    | some entry => pure entry

/-- Initialize or replace one temporary payload cell.  The event derives its
backing and extent from the pre-write storage even when the write is rejected. -/
def tempPayloadWrite? (storage : TempStorage κ ν) (index : Int)
    (entry : SortSliceEntry κ ν) : TraceResult (TempStorage κ ν) :=
  (arrayWrite? (.tempPayload storage.backing) storage.cells index (some entry)).map
    fun cells => { storage with cells := cells }

/-- Instrument a key-array read from the paired `SortSlice` representation.
The returned entry carries the synchronized payload so a caller can reproduce
the uninstrumented atomic representation, but this event records only the key
component. -/
def sortSliceKeysRead? (slice : SortSlice κ ν) (index : Int) :
    TraceResult (SortSliceEntry κ ν) :=
  captureAccess .read .inputKeys index slice.entries.size (slice.read? index)

/-- Instrument a synchronized-values read.  Call this only on paths on which
the C `values` pointer is present; the extent is always derived from `slice`. -/
def sortSliceValuesRead? (slice : SortSlice κ ν) (index : Int) :
    TraceResult (SortSliceEntry κ ν) :=
  captureAccess .read .synchronizedValues index slice.entries.size
    (slice.read? index)

/-- Instrument a key-array write through the exact `SortSlice.write?` result. -/
def sortSliceKeysWrite? (slice : SortSlice κ ν) (index : Int)
    (entry : SortSliceEntry κ ν) : TraceResult (SortSlice κ ν) :=
  captureAccess .write .inputKeys index slice.entries.size
    (slice.write? index entry)

/-- Instrument a synchronized-values write through the exact
`SortSlice.write?` result.  Call this only when the values array is present. -/
def sortSliceValuesWrite? (slice : SortSlice κ ν) (index : Int)
    (entry : SortSliceEntry κ ν) : TraceResult (SortSlice κ ν) :=
  captureAccess .write .synchronizedValues index slice.entries.size
    (slice.write? index entry)

/-- Read an indexed pending run from the current state.  Pushes use the
separate post-push-depth channel and never call this wrapper. -/
def pendingRunRead? (state : MergeState κ ν) (index : Int) :
    TraceResult PendingRun :=
  arrayRead? .pendingRuns state.pending index

/-- Replace an indexed pending run in the current state.  The event's extent
is the pending-array size before the attempted update. -/
def pendingRunWrite? (state : MergeState κ ν) (index : Int)
    (run : PendingRun) : TraceResult (MergeState κ ν) :=
  (arrayWrite? .pendingRuns state.pending index run).map fun pending =>
    { state with pending := pending }

/-- Update only the stored power field of one pending run while recording the
single indexed write performed by C.  Looking up the other fields is part of
constructing the replacement record, not a second source-level read event.
Rejected negative and out-of-range writes retain their attempted event. -/
def pendingRunPowerWrite? (state : MergeState κ ν) (index : Int)
    (power : Nat) : TraceResult (MergeState κ ν) :=
  let result :=
    if 0 ≤ index then
      state.pending[index.toNat]?.map fun top =>
        { state with
          pending := state.pending.setIfInBounds index.toNat
            ({ top with power := some power } : PendingRun) }
    else
      none
  captureAccess .write .pendingRuns index state.pending.size result

@[simp]
theorem trace_tempPayloadRead (storage : TempStorage κ ν) (index : Int) :
    (tempPayloadRead? storage index).trace =
      AccessTrace.singletonAccess .read (.tempPayload storage.backing)
        index storage.cells.size := by
  by_cases hNonnegative : 0 ≤ index
  · cases hCell : storage.cells[index.toNat]? with
    | none =>
        simp [tempPayloadRead?, trace_bind, arrayRead?, captureAccess,
          hNonnegative, hCell]
    | some cell =>
        cases cell <;>
          simp [tempPayloadRead?, trace_bind, arrayRead?, captureAccess,
            pure, failure, hNonnegative, hCell]
  · simp [tempPayloadRead?, trace_bind, arrayRead?, captureAccess,
      hNonnegative]

@[simp]
theorem trace_tempPayloadWrite (storage : TempStorage κ ν) (index : Int)
    (entry : SortSliceEntry κ ν) :
    (tempPayloadWrite? storage index entry).trace =
      AccessTrace.singletonAccess .write (.tempPayload storage.backing)
        index storage.cells.size := by
  rfl

@[simp]
theorem erase_tempPayloadRead (storage : TempStorage κ ν) (index : Int) :
    (tempPayloadRead? storage index).erase =
      if 0 ≤ index then storage.cells[index.toNat]?.bind id else none := by
  by_cases hNonnegative : 0 ≤ index
  · cases hCell : storage.cells[index.toNat]? with
    | none =>
        simp [tempPayloadRead?, hNonnegative, hCell]
    | some cell =>
        cases cell <;> simp [tempPayloadRead?, hNonnegative, hCell]
  · simp [tempPayloadRead?, hNonnegative]

@[simp]
theorem erase_tempPayloadWrite (storage : TempStorage κ ν) (index : Int)
    (entry : SortSliceEntry κ ν) :
    (tempPayloadWrite? storage index entry).erase =
      if 0 ≤ index ∧ index.toNat < storage.cells.size then
        some
          { storage with
            cells := storage.cells.setIfInBounds index.toNat (some entry) }
      else
        none := by
  by_cases hBounds : 0 ≤ index ∧ index.toNat < storage.cells.size <;>
    simp [tempPayloadWrite?, hBounds]

@[simp]
theorem erase_sortSliceKeysRead (slice : SortSlice κ ν) (index : Int) :
    (sortSliceKeysRead? slice index).erase = slice.read? index := by
  rfl

@[simp]
theorem erase_sortSliceValuesRead (slice : SortSlice κ ν) (index : Int) :
    (sortSliceValuesRead? slice index).erase = slice.read? index := by
  rfl

@[simp]
theorem erase_sortSliceKeysWrite (slice : SortSlice κ ν) (index : Int)
    (entry : SortSliceEntry κ ν) :
    (sortSliceKeysWrite? slice index entry).erase = slice.write? index entry := by
  rfl

@[simp]
theorem erase_sortSliceValuesWrite (slice : SortSlice κ ν) (index : Int)
    (entry : SortSliceEntry κ ν) :
    (sortSliceValuesWrite? slice index entry).erase = slice.write? index entry := by
  rfl

@[simp]
theorem trace_sortSliceKeysRead (slice : SortSlice κ ν) (index : Int) :
    (sortSliceKeysRead? slice index).trace =
      AccessTrace.singletonAccess .read .inputKeys index slice.entries.size := by
  rfl

@[simp]
theorem trace_sortSliceValuesRead (slice : SortSlice κ ν) (index : Int) :
    (sortSliceValuesRead? slice index).trace =
      AccessTrace.singletonAccess .read .synchronizedValues index
        slice.entries.size := by
  rfl

@[simp]
theorem trace_sortSliceKeysWrite (slice : SortSlice κ ν) (index : Int)
    (entry : SortSliceEntry κ ν) :
    (sortSliceKeysWrite? slice index entry).trace =
      AccessTrace.singletonAccess .write .inputKeys index slice.entries.size := by
  rfl

@[simp]
theorem trace_sortSliceValuesWrite (slice : SortSlice κ ν) (index : Int)
    (entry : SortSliceEntry κ ν) :
    (sortSliceValuesWrite? slice index entry).trace =
      AccessTrace.singletonAccess .write .synchronizedValues index
        slice.entries.size := by
  rfl

@[simp]
theorem erase_pendingRunRead (state : MergeState κ ν) (index : Int) :
    (pendingRunRead? state index).erase =
      if 0 ≤ index then state.pending[index.toNat]? else none := by
  rfl

@[simp]
theorem erase_pendingRunWrite (state : MergeState κ ν) (index : Int)
    (run : PendingRun) :
    (pendingRunWrite? state index run).erase =
      if 0 ≤ index ∧ index.toNat < state.pending.size then
        some
          { state with
            pending := state.pending.setIfInBounds index.toNat run }
      else
        none := by
  by_cases hBounds : 0 ≤ index ∧ index.toNat < state.pending.size <;>
    simp [pendingRunWrite?, hBounds]

@[simp]
theorem erase_pendingRunPowerWrite (state : MergeState κ ν) (index : Int)
    (power : Nat) :
    (pendingRunPowerWrite? state index power).erase =
      if 0 ≤ index then
        state.pending[index.toNat]?.map fun top =>
          { state with
            pending := state.pending.setIfInBounds index.toNat
              ({ top with power := some power } : PendingRun) }
      else
        none := by
  rfl

@[simp]
theorem trace_pendingRunRead (state : MergeState κ ν) (index : Int) :
    (pendingRunRead? state index).trace =
      AccessTrace.singletonAccess .read .pendingRuns index state.pending.size := by
  rfl

@[simp]
theorem trace_pendingRunWrite (state : MergeState κ ν) (index : Int)
    (run : PendingRun) :
    (pendingRunWrite? state index run).trace =
      AccessTrace.singletonAccess .write .pendingRuns index state.pending.size := by
  rfl

@[simp]
theorem trace_pendingRunPowerWrite (state : MergeState κ ν) (index : Int)
    (power : Nat) :
    (pendingRunPowerWrite? state index power).trace =
      AccessTrace.singletonAccess .write .pendingRuns index state.pending.size := by
  rfl

end TraceResult

/-- Instrument the unconditional pending-run push.  The state update is the
same unbounded `Array.push` used by `list_sort_impl`; keeping this core wrapper
dependent only on `MergeState` lets every local transcribed evaluator import
the trace API without a dependency cycle.

This low-level compatibility wrapper records only the post-push depth because
it is not given run-discovery or adaptive-minrun metadata.  The real scan loop
must use `pushFormedRunTraced` below when it records a formed leaf. -/
def pushPendingRunTraced (state : MergeState κ ν) (run : PendingRun) :
    TraceResult (MergeState κ ν) :=
  let pushed := { state with pending := state.pending.push run }
  { result := some pushed
    trace := AccessTrace.singletonPushDepth pushed.pending.size }

@[simp]
theorem erase_pushPendingRunTraced (state : MergeState κ ν) (run : PendingRun) :
    (pushPendingRunTraced state run).erase =
      some { state with pending := state.pending.push run } := by
  rfl

@[simp]
theorem trace_pushPendingRunTraced (state : MergeState κ ν) (run : PendingRun) :
    (pushPendingRunTraced state run).trace =
      AccessTrace.singletonPushDepth (state.pending.size + 1) := by
  simp [pushPendingRunTraced, AccessTrace.singletonPushDepth]

/-- Push a run formed by the scan loop and retain the adaptive-minrun context
needed to interpret that leaf later.  The run and depth are derived rather
than accepted as metadata, preventing those two fields from disagreeing with
the actual state transition. -/
def pushFormedRunTraced (state : MergeState κ ν) (run : PendingRun)
    (naturalLength target remainingBefore : Nat) :
    TraceResult (MergeState κ ν) :=
  let pushed := { state with pending := state.pending.push run }
  let event : PendingPushEvent :=
    { run := RunSpan.ofPendingRun run
      depthAfter := pushed.pending.size
      naturalLength := naturalLength
      target := target
      remainingBefore := remainingBefore }
  { result := some pushed
    trace := AccessTrace.singletonFormedRun event }

@[simp]
theorem erase_pushFormedRunTraced (state : MergeState κ ν) (run : PendingRun)
    (naturalLength target remainingBefore : Nat) :
    (pushFormedRunTraced state run naturalLength target remainingBefore).erase =
      some { state with pending := state.pending.push run } := by
  rfl

@[simp]
theorem trace_pushFormedRunTraced (state : MergeState κ ν) (run : PendingRun)
    (naturalLength target remainingBefore : Nat) :
    (pushFormedRunTraced state run naturalLength target remainingBefore).trace =
      AccessTrace.singletonFormedRun
        { run := RunSpan.ofPendingRun run
          depthAfter := state.pending.size + 1
          naturalLength := naturalLength
          target := target
          remainingBefore := remainingBefore } := by
  simp [pushFormedRunTraced, AccessTrace.singletonFormedRun]

/-- Adding the formed-run observation changes only the new policy-event
channel.  Result erasure and every pre-existing trace channel agree exactly
with the low-level unconditional-push wrapper. -/
theorem pushFormedRunTraced_legacyProjection
    (state : MergeState κ ν) (run : PendingRun)
    (naturalLength target remainingBefore : Nat) :
    (pushFormedRunTraced state run naturalLength target
        remainingBefore).erase =
        (pushPendingRunTraced state run).erase ∧
    (pushFormedRunTraced state run naturalLength target
        remainingBefore).trace.accesses =
        (pushPendingRunTraced state run).trace.accesses ∧
    (pushFormedRunTraced state run naturalLength target
        remainingBefore).trace.pushDepths =
        (pushPendingRunTraced state run).trace.pushDepths ∧
    (pushFormedRunTraced state run naturalLength target
        remainingBefore).trace.memoryEvents =
        (pushPendingRunTraced state run).trace.memoryEvents ∧
    (pushFormedRunTraced state run naturalLength target
        remainingBefore).trace.fuelExhausted =
        (pushPendingRunTraced state run).trace.fuelExhausted := by
  refine ⟨rfl, ?_⟩
  simp [pushFormedRunTraced, pushPendingRunTraced,
    AccessTrace.singletonFormedRun, AccessTrace.singletonPushDepth]

/-- Exact local policy observation for one successful formed-run push. -/
theorem pushFormedRunTraced_policyEvent
    (state : MergeState κ ν) (run : PendingRun)
    (naturalLength target remainingBefore : Nat) :
    (pushFormedRunTraced state run naturalLength target remainingBefore).trace.policyEvents =
      [.formed
        { run := RunSpan.ofPendingRun run
          depthAfter := state.pending.size + 1
          naturalLength := naturalLength
          target := target
          remainingBefore := remainingBefore }] ∧
    (pushFormedRunTraced state run naturalLength target remainingBefore).trace.pushDepths =
      [state.pending.size + 1] := by
  simp [trace_pushFormedRunTraced, AccessTrace.singletonFormedRun]

/-! ## Executable regressions -/

private def accessTraceRegressionRun : PendingRun :=
  { base := 0, len := 1, power := none }

/-- A concrete pending array at the C capacity, used only to demonstrate the
trace semantics without requiring an otherwise irrelevant `MergeState`. -/
private def accessTraceCapacityPending : Array PendingRun :=
  Array.replicate MAX_MERGE_PENDING accessTraceRegressionRun

/-- The same total push performed by `pushPendingRunTraced`, projected to the
pending array for a closed executable capacity regression. -/
private def accessTraceForcedPush : TraceResult (Array PendingRun) :=
  let pushed := accessTraceCapacityPending.push accessTraceRegressionRun
  { result := some pushed
    trace := AccessTrace.singletonPushDepth pushed.size }

/-- At depth 64 the modeled push physically succeeds and records 65.  The
trace has no capacity-failure or assertion-event channel that could make this
fact true vacuously. -/
theorem forcedPushAtCapacity_records65 :
    accessTraceForcedPush.result.map Array.size = some 65 ∧
      accessTraceForcedPush.trace.pushDepths = [65] ∧
      accessTraceForcedPush.trace.stackDepthMax = 65 := by
  decide

/-- Parametric form of the capacity regression for the actual `MergeState`
wrapper: it neither refuses nor clamps a 64-to-65 push. -/
theorem pushPendingRunTraced_at_capacity (state : MergeState κ ν)
    (run : PendingRun) (hDepth : state.pending.size = MAX_MERGE_PENDING) :
    (pushPendingRunTraced state run).result.map (fun pushed => pushed.pending.size) =
        some 65 ∧
      (pushPendingRunTraced state run).trace.pushDepths = [65] ∧
      (pushPendingRunTraced state run).trace.stackDepthMax = 65 := by
  simp [pushPendingRunTraced, hDepth, MAX_MERGE_PENDING,
    AccessTrace.singletonPushDepth, AccessTrace.stackDepthMax]

private def releasedTempStorage : TempStorage Nat Nat :=
  { cells := #[]
    backing := .released
    hasValues := true }

private def rejectedReleasedTempRead : TraceResult (SortSliceEntry Nat Nat) :=
  TraceResult.tempPayloadRead? releasedTempStorage 0

/-- A rejected temporary access is still recorded, so both its bad upper bound
and its released backing remain visible to their separate predicates. -/
theorem rejectedReleasedTempRead_is_observable :
    rejectedReleasedTempRead.result = none ∧
      rejectedReleasedTempRead.trace.accesses =
        [{ kind := .read, region := .tempPayload .released,
           index := 0, extent := 0 }] ∧
      ¬rejectedReleasedTempRead.trace.allAccessesInBounds ∧
      ¬rejectedReleasedTempRead.trace.tempPayloadAccessesLive := by
  decide

private def uninitializedTempStorage : TempStorage Nat Nat :=
  { cells := #[none]
    backing := .inline
    hasValues := true }

private def rejectedUninitializedTempRead :
    TraceResult (SortSliceEntry Nat Nat) :=
  TraceResult.tempPayloadRead? uninitializedTempStorage 0

/-- Rejection because a live in-bounds cell is uninitialized does not erase
the attempt or falsely fail either the bounds or backing-liveness predicate. -/
theorem rejectedUninitializedTempRead_is_observable :
    rejectedUninitializedTempRead.result = none ∧
      rejectedUninitializedTempRead.trace.accesses =
        [{ kind := .read, region := .tempPayload .inline,
           index := 0, extent := 1 }] ∧
      rejectedUninitializedTempRead.trace.allAccessesInBounds ∧
      rejectedUninitializedTempRead.trace.tempPayloadAccessesLive := by
  decide

private def orderedAccessSlice : SortSlice Nat Nat :=
  { entries :=
      #[{ key := 4, value := some 40 },
        { key := 9, value := some 90 }] }

private def orderedAccessRegression : TraceResult (SortSlice Nat Nat) :=
  (TraceResult.sortSliceKeysRead? orderedAccessSlice 1).bind fun entry =>
    TraceResult.sortSliceValuesWrite? orderedAccessSlice 0 entry

/-- Local evaluator composition keeps access attempts in execution order. -/
theorem localTraceComposition_preserves_order :
    orderedAccessRegression.trace.accesses =
      [{ kind := .read, region := .inputKeys, index := 1, extent := 2 },
       { kind := .write, region := .synchronizedValues, index := 0, extent := 2 }] ∧
      orderedAccessRegression.trace.allAccessesInBounds ∧
      orderedAccessRegression.trace.tempPayloadAccessesLive := by
  decide

end CPythonListsort
