/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Distributed.ChandyLamport
public import Mathlib.Data.Nat.Basic

/-!
# Tests for the consistency of the Chandy–Lamport snapshot cut

* Messages, processes and positions in `ℕ`, with two processes; every message goes from process
  `0` to process `1`. Process `0` records at position `1`, process `1` records at position `3`,
  and the marker from `0` reaches `1` at position `4`. Message `0` is sent at `0` and received
  at `2`; every later message is sent at `2`, after process `0` records, and received at `5`,
  after the marker, so the FIFO hypothesis holds without being vacuous. `snapshot_consistent`
  then shows that message `0`, received before process `1` records, was sent before process `0`
  records.
* The marker hypothesis cannot be dropped: if the marker reaches process `1` at position `0`,
  before process `1` records, a message sent at `2`, after process `0` records, may be received
  at `2`, before process `1` records, with the FIFO hypothesis still satisfied.
-/

@[expose] public section

namespace Cslib.Distributed.ChandyLamport.Tests

/-- Every message is sent by process `0`. -/
def src (_ : ℕ) : ℕ := 0

/-- Every message is received by process `1`. -/
def dst (_ : ℕ) : ℕ := 1

/-- Message `0` is sent at position `0`, every later message at position `2`. -/
def sendPos : ℕ → ℕ
  | 0 => 0
  | _ + 1 => 2

/-- Message `0` is received at position `2`, every later message at position `5`. -/
def recvPos : ℕ → ℕ
  | 0 => 2
  | _ + 1 => 5

/-- Process `0` records at position `1`, every other process at position `3`. -/
def cut : ℕ → ℕ
  | 0 => 1
  | _ + 1 => 3

/-- Every marker is received at position `4`. -/
def markerPos (_ _ : ℕ) : ℕ := 4

/-- Process `1` records at `3`, before the marker from process `0` arrives at `4`. -/
theorem hmarker (m : ℕ) : cut (dst m) ≤ markerPos (src m) (dst m) := by
  simp [cut, dst, markerPos]

/-- Only the messages after message `0` are sent at or after process `0` records, and they are
received at `5`, after the marker. -/
theorem hfifo (m : ℕ) (h : cut (src m) ≤ sendPos m) :
    markerPos (src m) (dst m) ≤ recvPos m := by
  cases m with
  | zero => exact absurd h (by decide)
  | succ k => simp [markerPos, recvPos]

/-- Message `1` is sent after process `0` records, so the FIFO hypothesis constrains it. -/
example : cut (src 1) ≤ sendPos 1 ∧ markerPos (src 1) (dst 1) ≤ recvPos 1 := by decide

/-- Message `0` is received before process `1` records, so it was sent before process `0`
records. -/
example : sendPos 0 < cut (src 0) :=
  snapshot_consistent src dst sendPos recvPos cut markerPos hmarker hfifo 0 (by decide)

/-- Without the marker hypothesis the cut can have an orphan message: with the marker at
position `0` and every message sent and received at position `2`, the FIFO hypothesis holds,
message `0` is received before process `1` records at `3`, and it is sent after process `0`
records at `1`. -/
example :
    ¬ ∀ (sendPos recvPos : ℕ → ℕ) (markerPos : ℕ → ℕ → ℕ),
      (∀ m, cut (src m) ≤ sendPos m → markerPos (src m) (dst m) ≤ recvPos m) →
      ∀ m, recvPos m < cut (dst m) → sendPos m < cut (src m) := by
  intro h
  have h0 := h (fun _ => 2) (fun _ => 2) (fun _ _ => 0) (fun _ _ => Nat.zero_le 2) 0
    (by decide)
  exact absurd h0 (by decide)

end Cslib.Distributed.ChandyLamport.Tests
