/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Literal acyclic path parents and exact source-generator bounds in this finite interval. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC422

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Exact raw parent and generator indices, before any finite generator decoding. -/
def y422TPathRawData70 : Fin 73 → ℕ × ℕ :=
  ![(8959, 6),
    (8960, 3),
    (8961, 0),
    (8962, 1),
    (8963, 5),
    (8964, 7),
    (8965, 2),
    (8966, 6),
    (8967, 3),
    (8968, 0),
    (8969, 1),
    (8970, 5),
    (8971, 7),
    (8972, 2),
    (8973, 6),
    (8974, 3),
    (8975, 0),
    (8976, 1),
    (8977, 5),
    (8978, 7),
    (8979, 2),
    (8980, 6),
    (8981, 3),
    (8982, 0),
    (8983, 1),
    (8984, 5),
    (8985, 7),
    (8986, 2),
    (8987, 6),
    (8988, 3),
    (8989, 0),
    (8990, 1),
    (8991, 5),
    (8992, 7),
    (128, 1),
    (8994, 0),
    (128, 3),
    (2341, 5),
    (128, 6),
    (128, 7),
    (2371, 3),
    (2371, 5),
    (2371, 6),
    (2371, 8),
    (8725, 4),
    (8725, 6),
    (8725, 8),
    (8267, 8),
    (8728, 8),
    (7983, 7),
    (8994, 2),
    (2384, 1),
    (3303, 0),
    (4349, 5),
    (3431, 0),
    (3744, 1),
    (5103, 2),
    (3248, 7),
    (9013, 0),
    (3139, 6),
    (3219, 0),
    (3367, 2),
    (2641, 0),
    (4349, 0),
    (4782, 1),
    (5712, 6),
    (4779, 1),
    (6468, 6),
    (6856, 1),
    (6728, 1),
    (9028, 0),
    (9029, 0),
    (1096, 1)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
-- Every nonroot parent is strictly earlier, and every source generator has its actual bound.
/-- Exact chronological parent and source-generator bounds for this whole finite interval. -/
theorem y422TPathRawData70_allowed (j : Fin 73) :
    (8960 + j.val = 0 ∨ (y422TPathRawData70 j).1 < 8960 + j.val) ∧
      (y422TPathRawData70 j).2 < 9 := by
  revert j
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
