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
def y422TPathRawData02 : Fin 128 → ℕ × ℕ :=
  ![(255, 7),
    (256, 2),
    (257, 6),
    (258, 3),
    (259, 0),
    (260, 1),
    (261, 5),
    (262, 7),
    (263, 2),
    (264, 6),
    (265, 3),
    (266, 0),
    (267, 1),
    (268, 5),
    (269, 7),
    (270, 2),
    (271, 6),
    (272, 3),
    (273, 0),
    (274, 1),
    (275, 5),
    (276, 7),
    (277, 2),
    (278, 6),
    (279, 3),
    (280, 0),
    (281, 1),
    (282, 5),
    (283, 7),
    (284, 2),
    (285, 6),
    (286, 3),
    (287, 0),
    (288, 1),
    (289, 5),
    (290, 7),
    (291, 2),
    (292, 6),
    (293, 3),
    (96, 8),
    (295, 5),
    (99, 7),
    (297, 1),
    (298, 2),
    (299, 0),
    (300, 5),
    (301, 6),
    (302, 0),
    (303, 7),
    (304, 8),
    (305, 1),
    (306, 2),
    (307, 0),
    (308, 5),
    (309, 6),
    (310, 0),
    (311, 7),
    (312, 8),
    (313, 0),
    (314, 1),
    (315, 2),
    (316, 0),
    (317, 5),
    (318, 6),
    (319, 0),
    (320, 7),
    (321, 8),
    (322, 0),
    (323, 1),
    (324, 2),
    (325, 0),
    (326, 5),
    (327, 6),
    (328, 0),
    (329, 7),
    (330, 8),
    (331, 0),
    (332, 1),
    (333, 2),
    (334, 0),
    (335, 5),
    (336, 6),
    (337, 0),
    (338, 7),
    (339, 8),
    (340, 0),
    (341, 1),
    (342, 2),
    (343, 0),
    (344, 5),
    (345, 6),
    (346, 0),
    (347, 7),
    (230, 0),
    (349, 1),
    (350, 5),
    (351, 7),
    (352, 2),
    (353, 6),
    (354, 3),
    (355, 4),
    (356, 0),
    (357, 1),
    (358, 5),
    (359, 7),
    (360, 2),
    (361, 6),
    (362, 3),
    (363, 0),
    (364, 1),
    (365, 5),
    (366, 7),
    (367, 2),
    (368, 6),
    (369, 3),
    (370, 0),
    (371, 1),
    (372, 5),
    (373, 7),
    (374, 2),
    (375, 6),
    (376, 3),
    (377, 0),
    (378, 1),
    (379, 5),
    (380, 7),
    (381, 2),
    (382, 6)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
-- Every nonroot parent is strictly earlier, and every source generator has its actual bound.
/-- Exact chronological parent and source-generator bounds for this whole finite interval. -/
theorem y422TPathRawData02_allowed (j : Fin 128) :
    (256 + j.val = 0 ∨ (y422TPathRawData02 j).1 < 256 + j.val) ∧
      (y422TPathRawData02 j).2 < 9 := by
  revert j
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
