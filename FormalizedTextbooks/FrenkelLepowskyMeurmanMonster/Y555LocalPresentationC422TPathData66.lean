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
def y422TPathRawData66 : Fin 128 → ℕ × ℕ :=
  ![(8447, 5),
    (8448, 7),
    (126, 3),
    (126, 6),
    (2369, 3),
    (8452, 2),
    (8453, 3),
    (2369, 5),
    (2369, 6),
    (8250, 4),
    (8250, 5),
    (8250, 6),
    (8253, 0),
    (8460, 5),
    (8461, 6),
    (8462, 7),
    (8463, 8),
    (8464, 0),
    (8465, 1),
    (8466, 2),
    (8467, 0),
    (8468, 5),
    (8469, 6),
    (8470, 0),
    (8471, 7),
    (8472, 8),
    (8473, 0),
    (8474, 1),
    (8475, 2),
    (8476, 0),
    (8477, 5),
    (8478, 6),
    (8479, 0),
    (8480, 7),
    (8481, 8),
    (8482, 0),
    (8483, 1),
    (8484, 2),
    (8485, 0),
    (8486, 5),
    (8487, 6),
    (8488, 0),
    (8489, 7),
    (8490, 8),
    (8491, 0),
    (8492, 1),
    (8493, 2),
    (8494, 0),
    (8495, 5),
    (8496, 6),
    (8497, 0),
    (8498, 7),
    (8499, 8),
    (8500, 0),
    (8501, 1),
    (8502, 2),
    (8503, 0),
    (8504, 5),
    (8505, 6),
    (8506, 0),
    (8507, 7),
    (8508, 8),
    (8509, 0),
    (8510, 1),
    (8511, 2),
    (8512, 0),
    (8513, 5),
    (8514, 6),
    (8515, 0),
    (8516, 7),
    (8517, 8),
    (8518, 0),
    (8519, 1),
    (8520, 2),
    (8521, 0),
    (8522, 5),
    (8523, 6),
    (8524, 0),
    (8525, 7),
    (8526, 8),
    (8527, 0),
    (8528, 1),
    (8529, 2),
    (8530, 0),
    (8531, 5),
    (8532, 6),
    (8533, 0),
    (8534, 7),
    (8535, 8),
    (8536, 0),
    (5726, 6),
    (8538, 3),
    (8539, 0),
    (8540, 1),
    (8541, 5),
    (8542, 7),
    (8543, 2),
    (8544, 6),
    (8545, 3),
    (8546, 0),
    (8547, 1),
    (8548, 5),
    (8549, 7),
    (8550, 2),
    (8551, 6),
    (8552, 3),
    (8553, 0),
    (8554, 1),
    (8555, 5),
    (8556, 7),
    (8557, 2),
    (8558, 6),
    (8559, 3),
    (8560, 0),
    (8561, 1),
    (8562, 5),
    (8563, 7),
    (8564, 2),
    (8565, 6),
    (8566, 3),
    (8567, 0),
    (8568, 1),
    (8569, 5),
    (8570, 7),
    (8571, 2),
    (8572, 6),
    (8573, 3),
    (8574, 0)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
-- Every nonroot parent is strictly earlier, and every source generator has its actual bound.
/-- Exact chronological parent and source-generator bounds for this whole finite interval. -/
theorem y422TPathRawData66_allowed (j : Fin 128) :
    (8448 + j.val = 0 ∨ (y422TPathRawData66 j).1 < 8448 + j.val) ∧
      (y422TPathRawData66 j).2 < 9 := by
  revert j
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
