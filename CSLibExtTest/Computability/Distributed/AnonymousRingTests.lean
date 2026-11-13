/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Distributed.AnonymousRing

/-!
# Tests for the anonymous-ring symmetry argument

* A concrete majority transition `maj` on a ring of three processes: the explicit configuration
  after two rounds from the all-`true` start is all-`true`, and `no_leader_election` rules out a
  unique leader in that run.
* The symmetric start is needed: on a ring of five processes, the asymmetric start
  `true, false, true, false, false` evolves under `maj` to exactly one `true` process (process
  `1`) after one round and to all-`false` after two.
-/

@[expose] public section

namespace Cslib.Distributed.AnonymousRing.Tests

/-- Majority vote of the left neighbor, the process itself and the right neighbor. -/
def maj (l c r : Bool) : Bool := (l && c) || (l && r) || (c && r)

/-- Two explicit rounds of `maj` from the all-`true` start on a 3-ring. -/
example : ∀ i : ZMod 3, ringState maj (fun _ => true) 2 i = true := by decide

/-- No unique leader in that run, with `L := id` ("my bit is set"). -/
example : ¬ ∃! i : ZMod 3, ringState maj (fun _ => true) 2 i = true :=
  no_leader_election maj (by decide) id (fun _ => true) (fun _ _ => rfl) 2

/-- An asymmetric start on a 5-ring: processes `0` and `2` are set. -/
def asym (i : ZMod 5) : Bool := decide (i = 0) || decide (i = 2)

/-- After one round exactly process `1` is set, so without a symmetric start a unique leader can
emerge: the hypothesis `h0` of `no_leader_election` is needed. -/
example : ∃! i : ZMod 5, ringState maj asym 1 i = true :=
  ⟨1, by decide, by decide⟩

/-- After two rounds every process is clear. -/
example : ∀ i : ZMod 5, ringState maj asym 2 i = false := by decide

end Cslib.Distributed.AnonymousRing.Tests
