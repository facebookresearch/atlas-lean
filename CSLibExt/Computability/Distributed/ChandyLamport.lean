/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Notation

/-!
# Consistency of the Chandy–Lamport snapshot cut

An abstract position model of the cut recorded by the Chandy–Lamport snapshot algorithm.
Messages are indexed by `ℕ`: message `m` is sent by process `src m` at position `sendPos m` and
received by process `dst m` at position `recvPos m`, where positions index one global order of
events. Process `p` records its local state at position `cut p`, and `markerPos i j` is the
position at which process `j` receives the marker that process `i` sends on its channel to `j`.

The marker rules of the algorithm enter as two hypotheses, stated only for the channels
`src m → dst m` that carry a message `m`:

* a process records its state no later than it receives a marker, so
  `cut (dst m) ≤ markerPos (src m) (dst m)`;
* a process sends its markers right after recording its state and channels are FIFO, so a
  message sent at or after its sender's recording point is received no earlier than the marker
  on its channel.

`snapshot_consistent`: under these hypotheses the recorded cut is consistent, that is, it has no
orphan messages: a message received before its receiver's recording point was sent before its
sender's recording point.

Only this consistency property is formalized. Executions of the algorithm, the sending of
markers, and the recording of channel states are not modeled.

## References

* K. M. Chandy and L. Lamport, *Distributed snapshots: determining global states of distributed
  systems*, ACM Transactions on Computer Systems 3(1), 1985.
-/

@[expose] public section

namespace Cslib.Distributed.ChandyLamport

/-- The cut recorded by a Chandy–Lamport snapshot has no orphan messages. Message `m` is sent by
`src m` at position `sendPos m` and received by `dst m` at position `recvPos m`; process `p`
records its state at position `cut p`, and `markerPos i j` is the position at which `j` receives
the marker from `i`. Suppose that on every channel carrying a message the receiver records no
later than it receives the marker (`hmarker`), and that every message sent at or after its
sender's recording point is received no earlier than the marker on its channel (`hfifo`). Then a
message received before its receiver's recording point was sent before its sender's recording
point. -/
theorem snapshot_consistent
    (src dst : ℕ → ℕ) (sendPos recvPos cut : ℕ → ℕ)
    (markerPos : ℕ → ℕ → ℕ)
    (hmarker : ∀ m, cut (dst m) ≤ markerPos (src m) (dst m))
    (hfifo : ∀ m, cut (src m) ≤ sendPos m →
      markerPos (src m) (dst m) ≤ recvPos m)
    (m : ℕ) (hrecv : recvPos m < cut (dst m)) :
    sendPos m < cut (src m) := by
  have h2 := hmarker m
  by_cases h : cut (src m) ≤ sendPos m
  · have h1 := hfifo m h
    omega
  · omega

end Cslib.Distributed.ChandyLamport
