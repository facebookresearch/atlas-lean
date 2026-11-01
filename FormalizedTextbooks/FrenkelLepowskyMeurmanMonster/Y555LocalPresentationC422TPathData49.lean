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
def y422TPathRawData49 : Fin 128 → ℕ × ℕ :=
  ![(6271, 2),
    (6272, 6),
    (6273, 3),
    (6274, 0),
    (6275, 1),
    (6276, 5),
    (6277, 7),
    (6278, 2),
    (6279, 6),
    (6280, 3),
    (6281, 0),
    (6282, 1),
    (6283, 5),
    (6284, 7),
    (6285, 2),
    (6286, 6),
    (6287, 3),
    (6288, 0),
    (6289, 1),
    (6290, 5),
    (6291, 7),
    (6292, 2),
    (6293, 6),
    (6294, 3),
    (6295, 0),
    (6296, 1),
    (6297, 5),
    (6298, 7),
    (6299, 2),
    (6300, 6),
    (6301, 3),
    (6302, 0),
    (6303, 1),
    (6304, 5),
    (6305, 7),
    (6306, 2),
    (6307, 6),
    (6308, 3),
    (6309, 4),
    (6310, 0),
    (6311, 1),
    (6312, 5),
    (6313, 7),
    (6314, 2),
    (6315, 6),
    (6316, 3),
    (6317, 0),
    (6318, 1),
    (6319, 5),
    (6320, 7),
    (6321, 2),
    (6322, 6),
    (6323, 3),
    (6324, 0),
    (6325, 1),
    (6326, 5),
    (6327, 7),
    (6328, 2),
    (6329, 6),
    (6330, 3),
    (6331, 0),
    (6332, 1),
    (6333, 5),
    (6334, 7),
    (6335, 2),
    (6336, 6),
    (6337, 3),
    (6338, 0),
    (6339, 1),
    (6340, 5),
    (6341, 7),
    (6342, 2),
    (6343, 6),
    (6344, 3),
    (6345, 0),
    (6346, 1),
    (6347, 5),
    (6348, 7),
    (6349, 2),
    (6350, 6),
    (6351, 3),
    (6352, 0),
    (6353, 1),
    (6354, 5),
    (6355, 7),
    (6356, 2),
    (6357, 6),
    (6358, 3),
    (6359, 0),
    (6360, 1),
    (6361, 5),
    (6362, 7),
    (6363, 2),
    (6364, 6),
    (6365, 3),
    (6366, 0),
    (6367, 1),
    (6368, 5),
    (6369, 7),
    (2363, 3),
    (2364, 0),
    (118, 3),
    (6373, 2),
    (6374, 3),
    (118, 6),
    (6180, 4),
    (6180, 5),
    (6180, 6),
    (6180, 8),
    (5706, 7),
    (5985, 6),
    (4997, 8),
    (6383, 0),
    (6384, 1),
    (6385, 2),
    (6386, 0),
    (6387, 5),
    (6388, 6),
    (6389, 0),
    (6390, 7),
    (6391, 8),
    (6392, 0),
    (6393, 1),
    (6394, 2),
    (6395, 0),
    (6396, 5),
    (6397, 6),
    (6398, 0)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
-- Every nonroot parent is strictly earlier, and every source generator has its actual bound.
/-- Exact chronological parent and source-generator bounds for this whole finite interval. -/
theorem y422TPathRawData49_allowed (j : Fin 128) :
    (6272 + j.val = 0 ∨ (y422TPathRawData49 j).1 < 6272 + j.val) ∧
      (y422TPathRawData49 j).2 < 9 := by
  revert j
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
