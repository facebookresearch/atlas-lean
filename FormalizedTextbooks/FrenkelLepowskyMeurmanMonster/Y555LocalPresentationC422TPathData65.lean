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
def y422TPathRawData65 : Fin 128 → ℕ × ℕ :=
  ![(8319, 5),
    (8320, 7),
    (8321, 2),
    (8322, 6),
    (8323, 3),
    (8324, 4),
    (8325, 0),
    (8326, 1),
    (8327, 5),
    (8328, 7),
    (8329, 2),
    (8330, 6),
    (8331, 3),
    (8332, 0),
    (8333, 1),
    (8334, 5),
    (8335, 7),
    (8336, 2),
    (8337, 6),
    (8338, 3),
    (8339, 0),
    (8340, 1),
    (8341, 5),
    (8342, 7),
    (8343, 2),
    (8344, 6),
    (8345, 3),
    (8346, 0),
    (8347, 1),
    (8348, 5),
    (8349, 7),
    (8350, 2),
    (8351, 6),
    (8352, 3),
    (8353, 0),
    (8354, 1),
    (8355, 5),
    (8356, 7),
    (8357, 2),
    (8358, 6),
    (8359, 3),
    (8360, 0),
    (8361, 1),
    (8362, 5),
    (8363, 7),
    (8364, 2),
    (8365, 6),
    (8366, 3),
    (8367, 0),
    (8368, 1),
    (8369, 5),
    (8370, 7),
    (8371, 2),
    (8372, 6),
    (8373, 3),
    (8374, 0),
    (8375, 1),
    (8376, 5),
    (8377, 7),
    (8378, 2),
    (8379, 6),
    (8380, 3),
    (8381, 0),
    (8382, 1),
    (8383, 5),
    (8384, 7),
    (8385, 2),
    (8386, 6),
    (8387, 3),
    (8388, 4),
    (8389, 0),
    (8390, 1),
    (8391, 5),
    (8392, 7),
    (8393, 2),
    (8394, 6),
    (8395, 3),
    (8396, 0),
    (8397, 1),
    (8398, 5),
    (8399, 7),
    (8400, 2),
    (8401, 6),
    (8402, 3),
    (8403, 0),
    (8404, 1),
    (8405, 5),
    (8406, 7),
    (8407, 2),
    (8408, 6),
    (8409, 3),
    (8410, 0),
    (8411, 1),
    (8412, 5),
    (8413, 7),
    (8414, 2),
    (8415, 6),
    (8416, 3),
    (8417, 0),
    (8418, 1),
    (8419, 5),
    (8420, 7),
    (8421, 2),
    (8422, 6),
    (8423, 3),
    (8424, 0),
    (8425, 1),
    (8426, 5),
    (8427, 7),
    (8428, 2),
    (8429, 6),
    (8430, 3),
    (8431, 0),
    (8432, 1),
    (8433, 5),
    (8434, 7),
    (8435, 2),
    (8436, 6),
    (8437, 3),
    (8438, 0),
    (8439, 1),
    (8440, 5),
    (8441, 7),
    (8442, 2),
    (8443, 6),
    (8444, 3),
    (8445, 0),
    (8446, 1)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
-- Every nonroot parent is strictly earlier, and every source generator has its actual bound.
/-- Exact chronological parent and source-generator bounds for this whole finite interval. -/
theorem y422TPathRawData65_allowed (j : Fin 128) :
    (8320 + j.val = 0 ∨ (y422TPathRawData65 j).1 < 8320 + j.val) ∧
      (y422TPathRawData65 j).2 < 9 := by
  revert j
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
