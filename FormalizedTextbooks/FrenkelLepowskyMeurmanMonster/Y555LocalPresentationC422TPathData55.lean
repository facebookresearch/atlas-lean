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
def y422TPathRawData55 : Fin 128 → ℕ × ℕ :=
  ![(7039, 5),
    (7040, 7),
    (7041, 2),
    (7042, 6),
    (7043, 3),
    (7044, 0),
    (7045, 1),
    (7046, 5),
    (7047, 7),
    (7048, 2),
    (7049, 6),
    (7050, 3),
    (7051, 0),
    (7052, 1),
    (7053, 5),
    (7054, 7),
    (7055, 2),
    (7056, 6),
    (7057, 3),
    (7058, 0),
    (7059, 1),
    (7060, 5),
    (7061, 7),
    (7062, 2),
    (7063, 6),
    (7064, 3),
    (7065, 0),
    (7066, 1),
    (7067, 5),
    (7068, 7),
    (7069, 2),
    (7070, 6),
    (7071, 3),
    (7072, 0),
    (7073, 1),
    (7074, 5),
    (7075, 7),
    (7076, 2),
    (7077, 6),
    (7078, 3),
    (7079, 0),
    (7080, 1),
    (7081, 5),
    (7082, 7),
    (7083, 2),
    (7084, 6),
    (7085, 3),
    (7086, 0),
    (7087, 1),
    (7088, 5),
    (7089, 7),
    (7090, 2),
    (7091, 6),
    (7092, 3),
    (7093, 4),
    (7094, 0),
    (7095, 1),
    (7096, 5),
    (7097, 7),
    (7098, 2),
    (7099, 6),
    (7100, 3),
    (7101, 0),
    (7102, 1),
    (7103, 5),
    (7104, 7),
    (7105, 2),
    (7106, 6),
    (7107, 3),
    (7108, 0),
    (7109, 1),
    (7110, 5),
    (7111, 7),
    (7112, 2),
    (7113, 6),
    (7114, 3),
    (7115, 0),
    (7116, 1),
    (7117, 5),
    (7118, 7),
    (7119, 2),
    (7120, 6),
    (7121, 3),
    (7122, 0),
    (7123, 1),
    (7124, 5),
    (7125, 7),
    (7126, 2),
    (7127, 6),
    (7128, 3),
    (7129, 0),
    (7130, 1),
    (7131, 5),
    (7132, 7),
    (7133, 2),
    (7134, 6),
    (7135, 3),
    (7136, 0),
    (7137, 1),
    (7138, 5),
    (7139, 7),
    (7140, 2),
    (7141, 6),
    (7142, 3),
    (7143, 0),
    (7144, 1),
    (7145, 5),
    (7146, 7),
    (7147, 2),
    (7148, 6),
    (7149, 3),
    (7150, 0),
    (7151, 1),
    (7152, 5),
    (7153, 7),
    (6643, 3),
    (6643, 7),
    (2364, 3),
    (7157, 2),
    (7158, 3),
    (6895, 4),
    (6895, 6),
    (6895, 7),
    (6895, 8),
    (121, 7),
    (2503, 2),
    (7165, 5),
    (7166, 0)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
-- Every nonroot parent is strictly earlier, and every source generator has its actual bound.
/-- Exact chronological parent and source-generator bounds for this whole finite interval. -/
theorem y422TPathRawData55_allowed (j : Fin 128) :
    (7040 + j.val = 0 ∨ (y422TPathRawData55 j).1 < 7040 + j.val) ∧
      (y422TPathRawData55 j).2 < 9 := by
  revert j
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
