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
def y422TPathRawData47 : Fin 128 → ℕ × ℕ :=
  ![(6015, 7),
    (6016, 2),
    (6017, 6),
    (6018, 3),
    (6019, 0),
    (6020, 1),
    (6021, 5),
    (6022, 7),
    (6023, 2),
    (6024, 6),
    (6025, 3),
    (6026, 0),
    (6027, 1),
    (6028, 5),
    (6029, 7),
    (6030, 2),
    (6031, 6),
    (6032, 3),
    (6033, 0),
    (6034, 1),
    (6035, 5),
    (6036, 7),
    (6037, 2),
    (6038, 6),
    (6039, 3),
    (6040, 0),
    (6041, 1),
    (6042, 5),
    (6043, 7),
    (6044, 2),
    (6045, 6),
    (6046, 3),
    (6047, 0),
    (6048, 1),
    (6049, 5),
    (6050, 7),
    (6051, 2),
    (6052, 6),
    (6053, 3),
    (6054, 4),
    (6055, 0),
    (6056, 1),
    (6057, 5),
    (6058, 7),
    (6059, 2),
    (6060, 6),
    (6061, 3),
    (6062, 0),
    (6063, 1),
    (6064, 5),
    (6065, 7),
    (6066, 2),
    (6067, 6),
    (6068, 3),
    (6069, 0),
    (6070, 1),
    (6071, 5),
    (6072, 7),
    (6073, 2),
    (6074, 6),
    (6075, 3),
    (6076, 0),
    (6077, 1),
    (6078, 5),
    (6079, 7),
    (6080, 2),
    (6081, 6),
    (6082, 3),
    (6083, 0),
    (6084, 1),
    (6085, 5),
    (6086, 7),
    (6087, 2),
    (6088, 6),
    (6089, 3),
    (6090, 0),
    (6091, 1),
    (6092, 5),
    (6093, 7),
    (6094, 2),
    (6095, 6),
    (6096, 3),
    (6097, 0),
    (6098, 1),
    (6099, 5),
    (6100, 7),
    (6101, 2),
    (6102, 6),
    (6103, 3),
    (6104, 0),
    (6105, 1),
    (6106, 5),
    (6107, 7),
    (6108, 2),
    (6109, 6),
    (6110, 3),
    (6111, 0),
    (6112, 1),
    (6113, 5),
    (6114, 7),
    (6115, 2),
    (6116, 6),
    (6117, 3),
    (6118, 4),
    (6119, 0),
    (6120, 1),
    (6121, 5),
    (6122, 7),
    (6123, 2),
    (6124, 6),
    (6125, 3),
    (6126, 0),
    (6127, 1),
    (6128, 5),
    (6129, 7),
    (6130, 2),
    (6131, 6),
    (6132, 3),
    (6133, 0),
    (6134, 1),
    (6135, 5),
    (6136, 7),
    (6137, 2),
    (6138, 6),
    (6139, 3),
    (6140, 0),
    (6141, 1),
    (6142, 5)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
-- Every nonroot parent is strictly earlier, and every source generator has its actual bound.
/-- Exact chronological parent and source-generator bounds for this whole finite interval. -/
theorem y422TPathRawData47_allowed (j : Fin 128) :
    (6016 + j.val = 0 ∨ (y422TPathRawData47 j).1 < 6016 + j.val) ∧
      (y422TPathRawData47 j).2 < 9 := by
  revert j
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
