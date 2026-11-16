/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Distributed.SnapshotConsistency

@[expose] public section

/-- With every cut at position 1, a receive at position 0 forces the
corresponding send position below 1. -/
example : (0 : ℕ) < 1 :=
  snapshot_consistent (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0)
    (fun _ => 1) (fun _ _ => 1) (fun _ _ => le_refl 1)
    (fun _ h => absurd h (by decide)) 0 (by decide)

end
