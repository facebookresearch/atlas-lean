/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Basic

/-!
# Snapshot consistency

An abstract position model of a Chandy-Lamport snapshot:
message send and receive positions, per-process recording
points, and marker receive positions, with the FIFO and
marker hypotheses. Channel-state recording is not included
here.
-/

@[expose] public section

/-- Chandy-Lamport snapshot consistency, abstract
position model (core of DPA-06). Messages are indexed by
`ℕ`; `src m`, `dst m` are sender/receiver, `sendPos m`,
`recvPos m` their positions in the global event order.
`cut p` is process `p`'s recording point (first of its own
snapshot or a marker), and `markerPos i j` is when `j`
receives `i`'s marker. Hypotheses: markers are received no
earlier than the receiver's cut, and any message sent at or
after the sender's cut is received no earlier than the
sender's marker at the receiver (FIFO + marker rule). -/
theorem snapshot_consistent
    (src dst : ℕ → ℕ) (sendPos recvPos cut : ℕ → ℕ)
    (markerPos : ℕ → ℕ → ℕ)
    (hmarker : ∀ i j, cut j ≤ markerPos i j)
    (hfifo : ∀ m, cut (src m) ≤ sendPos m →
      markerPos (src m) (dst m) ≤ recvPos m)
    (m : ℕ) (hrecv : recvPos m < cut (dst m)) :
    sendPos m < cut (src m) := by
  by_contra h
  have hle : cut (src m) ≤ sendPos m := Nat.le_of_not_lt h
  have h1 := hfifo m hle
  have h2 := hmarker (src m) (dst m)
  omega

end
