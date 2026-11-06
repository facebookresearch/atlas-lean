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
def y422TPathRawData50 : Fin 128 → ℕ × ℕ :=
  ![(6399, 7),
    (6400, 8),
    (6401, 0),
    (6402, 1),
    (6403, 2),
    (6404, 0),
    (6405, 5),
    (6406, 6),
    (6407, 0),
    (6408, 7),
    (6409, 8),
    (6410, 0),
    (6411, 1),
    (6412, 2),
    (6413, 0),
    (6414, 5),
    (6415, 6),
    (6416, 0),
    (6417, 7),
    (6418, 8),
    (6419, 0),
    (6420, 1),
    (6421, 2),
    (6422, 0),
    (6423, 5),
    (6424, 6),
    (6425, 0),
    (6426, 7),
    (6427, 8),
    (6428, 0),
    (6429, 1),
    (6430, 2),
    (6431, 0),
    (6432, 5),
    (6433, 6),
    (6434, 0),
    (6435, 7),
    (6436, 8),
    (6437, 0),
    (6438, 1),
    (6439, 2),
    (6440, 0),
    (6441, 5),
    (6442, 6),
    (6443, 0),
    (6444, 7),
    (6445, 8),
    (6446, 0),
    (6447, 1),
    (6448, 2),
    (6449, 0),
    (6450, 5),
    (6451, 6),
    (6452, 0),
    (6453, 7),
    (6454, 8),
    (6455, 0),
    (6456, 1),
    (856, 7),
    (6458, 6),
    (6459, 3),
    (6460, 0),
    (6461, 1),
    (6462, 5),
    (6463, 7),
    (6464, 2),
    (6465, 6),
    (6466, 3),
    (6467, 0),
    (6468, 1),
    (6469, 5),
    (6470, 7),
    (6471, 2),
    (6472, 6),
    (6473, 3),
    (6474, 0),
    (6475, 1),
    (6476, 5),
    (6477, 7),
    (6478, 2),
    (6479, 6),
    (6480, 3),
    (6481, 0),
    (6482, 1),
    (6483, 5),
    (6484, 7),
    (6485, 2),
    (6486, 6),
    (6487, 3),
    (6488, 0),
    (6489, 1),
    (6490, 5),
    (6491, 7),
    (6492, 2),
    (6493, 6),
    (6494, 3),
    (6495, 0),
    (6496, 1),
    (6497, 5),
    (6498, 7),
    (6499, 2),
    (6500, 6),
    (6501, 3),
    (6502, 0),
    (6503, 1),
    (6504, 5),
    (6505, 7),
    (6506, 2),
    (6507, 6),
    (6508, 3),
    (6509, 0),
    (6510, 1),
    (6511, 5),
    (6512, 7),
    (6513, 2),
    (6514, 6),
    (6515, 3),
    (6516, 4),
    (6517, 0),
    (6518, 1),
    (6519, 5),
    (6520, 7),
    (6521, 2),
    (6522, 6),
    (6523, 3),
    (6524, 0),
    (6525, 1),
    (6526, 5)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
-- Every nonroot parent is strictly earlier, and every source generator has its actual bound.
/-- Exact chronological parent and source-generator bounds for this whole finite interval. -/
theorem y422TPathRawData50_allowed (j : Fin 128) :
    (6400 + j.val = 0 ∨ (y422TPathRawData50 j).1 < 6400 + j.val) ∧
      (y422TPathRawData50 j).2 < 9 := by
  revert j
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
