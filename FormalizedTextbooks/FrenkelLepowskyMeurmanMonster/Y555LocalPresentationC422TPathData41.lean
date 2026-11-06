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
def y422TPathRawData41 : Fin 128 → ℕ × ℕ :=
  ![(5247, 1),
    (5248, 2),
    (5249, 0),
    (5250, 5),
    (5251, 6),
    (5252, 0),
    (5253, 7),
    (5254, 8),
    (5255, 0),
    (5256, 1),
    (5257, 2),
    (5258, 0),
    (5259, 5),
    (5260, 6),
    (5261, 0),
    (5262, 7),
    (5263, 8),
    (5264, 0),
    (5265, 1),
    (2593, 7),
    (4217, 1),
    (5268, 5),
    (5269, 7),
    (5270, 2),
    (5271, 6),
    (5272, 3),
    (5273, 0),
    (5274, 1),
    (5275, 5),
    (5276, 7),
    (5277, 2),
    (5278, 6),
    (5279, 3),
    (5280, 0),
    (5281, 1),
    (5282, 5),
    (5283, 7),
    (5284, 2),
    (5285, 6),
    (5286, 3),
    (5287, 0),
    (5288, 1),
    (5289, 5),
    (5290, 7),
    (5291, 2),
    (5292, 6),
    (5293, 3),
    (5294, 0),
    (5295, 1),
    (5296, 5),
    (5297, 7),
    (5298, 2),
    (5299, 6),
    (5300, 3),
    (5301, 0),
    (5302, 1),
    (5303, 5),
    (5304, 7),
    (5305, 2),
    (5306, 6),
    (5307, 3),
    (5308, 0),
    (5309, 1),
    (5310, 5),
    (5311, 7),
    (5312, 2),
    (5313, 6),
    (5314, 3),
    (5315, 0),
    (5316, 1),
    (5317, 5),
    (5318, 7),
    (5319, 2),
    (5320, 6),
    (5321, 3),
    (5322, 4),
    (5323, 0),
    (5324, 1),
    (5325, 5),
    (5326, 7),
    (5327, 2),
    (5328, 6),
    (5329, 3),
    (5330, 0),
    (5331, 1),
    (5332, 5),
    (5333, 7),
    (5334, 2),
    (5335, 6),
    (5336, 3),
    (5337, 0),
    (5338, 1),
    (5339, 5),
    (5340, 7),
    (5341, 2),
    (5342, 6),
    (5343, 3),
    (5344, 0),
    (5345, 1),
    (5346, 5),
    (5347, 7),
    (5348, 2),
    (5349, 6),
    (5350, 3),
    (5351, 0),
    (5352, 1),
    (5353, 5),
    (5354, 7),
    (5355, 2),
    (5356, 6),
    (5357, 3),
    (5358, 0),
    (5359, 1),
    (5360, 5),
    (5361, 7),
    (5362, 2),
    (5363, 6),
    (5364, 3),
    (5365, 0),
    (5366, 1),
    (5367, 5),
    (5368, 7),
    (5369, 2),
    (5370, 6),
    (5371, 3),
    (5372, 0),
    (5373, 1),
    (5374, 5)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
-- Every nonroot parent is strictly earlier, and every source generator has its actual bound.
/-- Exact chronological parent and source-generator bounds for this whole finite interval. -/
theorem y422TPathRawData41_allowed (j : Fin 128) :
    (5248 + j.val = 0 ∨ (y422TPathRawData41 j).1 < 5248 + j.val) ∧
      (y422TPathRawData41 j).2 < 9 := by
  revert j
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
