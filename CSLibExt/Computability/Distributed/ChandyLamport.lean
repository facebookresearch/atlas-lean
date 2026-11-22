/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Order.Defs.LinearOrder

/-!
# Consistency of the Chandy–Lamport snapshot cut

An abstract position model of the cut recorded by the Chandy–Lamport snapshot algorithm.
Messages range over a type `M` and processes over a type `P`, and events occur at positions in a
linear order `T`, one global order of events. Message `m` is sent by process `src m` at position
`sendPos m` and received by process `dst m` at position `recvPos m`. Process `p` records its
local state at position `cut p`, and `markerPos i j` is the position at which process `j`
receives the marker that process `i` sends on its channel to `j`.

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
theorem snapshot_consistent {M P T : Type*} [LinearOrder T]
    (src dst : M → P) (sendPos recvPos : M → T) (cut : P → T)
    (markerPos : P → P → T)
    (hmarker : ∀ m, cut (dst m) ≤ markerPos (src m) (dst m))
    (hfifo : ∀ m, cut (src m) ≤ sendPos m →
      markerPos (src m) (dst m) ≤ recvPos m)
    (m : M) (hrecv : recvPos m < cut (dst m)) :
    sendPos m < cut (src m) :=
  not_le.mp fun hle => not_le.mpr hrecv (le_trans (hmarker m) (hfifo m hle))

end Cslib.Distributed.ChandyLamport
