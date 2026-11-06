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
def y422TPathRawData42 : Fin 128 → ℕ × ℕ :=
  ![(5375, 7),
    (5376, 2),
    (5377, 6),
    (5378, 3),
    (5379, 0),
    (5380, 1),
    (5381, 5),
    (5382, 7),
    (5383, 2),
    (5384, 6),
    (5385, 3),
    (5386, 4),
    (5387, 0),
    (5388, 1),
    (5389, 5),
    (5390, 7),
    (5391, 2),
    (5392, 6),
    (5393, 3),
    (5394, 0),
    (5395, 1),
    (5396, 5),
    (5397, 7),
    (5398, 2),
    (5399, 6),
    (5400, 3),
    (5401, 0),
    (5402, 1),
    (5403, 5),
    (5404, 7),
    (5405, 2),
    (5406, 6),
    (5407, 3),
    (5408, 0),
    (5409, 1),
    (5410, 5),
    (5411, 7),
    (5412, 2),
    (5413, 6),
    (5414, 3),
    (5415, 0),
    (5416, 1),
    (5417, 5),
    (5418, 7),
    (5419, 2),
    (5420, 6),
    (5421, 3),
    (5422, 0),
    (5423, 1),
    (5424, 5),
    (5425, 7),
    (5426, 2),
    (5427, 6),
    (5428, 3),
    (5429, 0),
    (5430, 1),
    (5431, 5),
    (5432, 7),
    (5433, 2),
    (5434, 6),
    (5435, 3),
    (5436, 0),
    (5437, 1),
    (5438, 5),
    (5439, 7),
    (5440, 2),
    (5441, 6),
    (5442, 3),
    (5443, 0),
    (5193, 3),
    (5193, 7),
    (5193, 8),
    (3463, 3),
    (5448, 2),
    (5449, 3),
    (3463, 8),
    (5194, 4),
    (5194, 5),
    (5194, 7),
    (5194, 8),
    (335, 8),
    (5456, 0),
    (5457, 1),
    (5458, 2),
    (2310, 7),
    (5460, 8),
    (5461, 0),
    (5462, 1),
    (5463, 2),
    (5464, 0),
    (5465, 5),
    (5466, 6),
    (5467, 0),
    (5468, 7),
    (5469, 8),
    (5470, 0),
    (5471, 1),
    (5472, 2),
    (5473, 0),
    (5474, 5),
    (5475, 6),
    (5476, 0),
    (5477, 7),
    (5478, 8),
    (5479, 0),
    (5480, 1),
    (5481, 2),
    (5482, 0),
    (5483, 5),
    (5484, 6),
    (5485, 0),
    (5486, 7),
    (5487, 8),
    (5488, 0),
    (5489, 1),
    (5490, 2),
    (5491, 0),
    (5492, 5),
    (5493, 6),
    (5494, 0),
    (5495, 7),
    (5496, 8),
    (5497, 0),
    (5498, 1),
    (5499, 2),
    (5500, 0),
    (5501, 5),
    (5502, 6)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
-- Every nonroot parent is strictly earlier, and every source generator has its actual bound.
/-- Exact chronological parent and source-generator bounds for this whole finite interval. -/
theorem y422TPathRawData42_allowed (j : Fin 128) :
    (5376 + j.val = 0 ∨ (y422TPathRawData42 j).1 < 5376 + j.val) ∧
      (y422TPathRawData42 j).2 < 9 := by
  revert j
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
