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
def y422TPathRawData03 : Fin 128 → ℕ × ℕ :=
  ![(383, 3),
    (384, 0),
    (385, 1),
    (386, 5),
    (387, 7),
    (388, 2),
    (389, 6),
    (390, 3),
    (391, 0),
    (392, 1),
    (393, 5),
    (394, 7),
    (395, 2),
    (396, 6),
    (397, 3),
    (398, 0),
    (399, 1),
    (400, 5),
    (401, 7),
    (402, 2),
    (403, 6),
    (404, 3),
    (405, 0),
    (406, 1),
    (407, 5),
    (408, 7),
    (409, 2),
    (410, 6),
    (411, 3),
    (412, 0),
    (413, 1),
    (414, 5),
    (415, 7),
    (416, 2),
    (417, 6),
    (418, 3),
    (36, 4),
    (420, 0),
    (421, 1),
    (422, 5),
    (423, 7),
    (424, 2),
    (425, 6),
    (426, 3),
    (427, 0),
    (428, 1),
    (429, 5),
    (430, 7),
    (431, 2),
    (432, 6),
    (433, 3),
    (434, 0),
    (435, 1),
    (436, 5),
    (437, 7),
    (438, 2),
    (439, 6),
    (440, 3),
    (441, 0),
    (442, 1),
    (443, 5),
    (444, 7),
    (445, 2),
    (446, 6),
    (447, 3),
    (448, 0),
    (449, 1),
    (450, 5),
    (451, 7),
    (452, 2),
    (453, 6),
    (454, 3),
    (455, 0),
    (456, 1),
    (457, 5),
    (458, 7),
    (459, 2),
    (460, 6),
    (461, 3),
    (462, 0),
    (463, 1),
    (464, 5),
    (465, 7),
    (466, 2),
    (467, 6),
    (468, 3),
    (469, 0),
    (470, 1),
    (471, 5),
    (472, 7),
    (473, 2),
    (474, 6),
    (475, 3),
    (476, 0),
    (477, 1),
    (478, 5),
    (479, 7),
    (480, 2),
    (481, 6),
    (482, 3),
    (483, 4),
    (484, 0),
    (485, 1),
    (486, 5),
    (487, 7),
    (488, 2),
    (489, 6),
    (151, 2),
    (491, 6),
    (492, 3),
    (83, 1),
    (77, 5),
    (74, 6),
    (71, 7),
    (241, 2),
    (498, 6),
    (499, 1),
    (208, 1),
    (501, 5),
    (502, 7),
    (503, 2),
    (504, 6),
    (505, 3),
    (506, 0),
    (507, 1),
    (508, 5),
    (509, 7),
    (510, 2)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
-- Every nonroot parent is strictly earlier, and every source generator has its actual bound.
/-- Exact chronological parent and source-generator bounds for this whole finite interval. -/
theorem y422TPathRawData03_allowed (j : Fin 128) :
    (384 + j.val = 0 ∨ (y422TPathRawData03 j).1 < 384 + j.val) ∧
      (y422TPathRawData03 j).2 < 9 := by
  revert j
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
