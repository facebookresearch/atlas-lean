/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Distributed.VectorClock

/-!
# Tests for vector clocks

The execution of `LamportClockTests`: `p0` has an internal event and then sends
a message, `p1` has an internal event and then receives that message, and `p0`
has another internal event.

* The vector timestamps are `(1, 0), (2, 0), (0, 1), (2, 2), (3, 0)`.
* The send happened before the receipt, and its timestamp is smaller.
* Unlike Lamport timestamps, vector timestamps detect concurrency: the internal
  events `2` of `p1` and `4` of `p0` have incomparable timestamps, so neither
  happened before the other.
-/

@[expose] public section

namespace Cslib.Distributed.VectorClock.Tests

open LamportClock

/-- The example execution. -/
def tr : List (Event (Fin 2)) :=
  [⟨0, none⟩, ⟨0, none⟩, ⟨1, none⟩, ⟨1, some 1⟩, ⟨0, none⟩]

example : (timestamps tr).map (fun v => [v 0, v 1]) =
    [[1, 0], [2, 0], [0, 1], [2, 2], [3, 0]] := by decide

/-- The send of event `1` happened before its receipt `3`. -/
example : HappensBefore tr 1 3 :=
  (happensBefore_iff_lt (by decide) (by decide)).2
    (Pi.lt_def.2 ⟨fun i => by revert i; decide, 1, by decide⟩)

/-- Events `2` and `4` are concurrent. -/
example : ¬ HappensBefore tr 2 4 ∧ ¬ HappensBefore tr 4 2 :=
  ⟨fun h => absurd (((happensBefore_iff_lt (by decide) (by decide)).1 h).le 1) (by decide),
    fun h => absurd (((happensBefore_iff_lt (by decide) (by decide)).1 h).le 0) (by decide)⟩

/-- Event `0` happened before event `3`, through process order and the
message. -/
example : HappensBefore tr 0 3 :=
  (happensBefore_iff_lt (by decide) (by decide)).2
    (Pi.lt_def.2 ⟨fun i => by revert i; decide, 0, by decide⟩)

end Cslib.Distributed.VectorClock.Tests
