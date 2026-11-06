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
def y422TPathRawData58 : Fin 128 → ℕ × ℕ :=
  ![(7423, 1),
    (7424, 5),
    (7425, 7),
    (122, 1),
    (122, 3),
    (123, 0),
    (7429, 7),
    (2365, 3),
    (7431, 2),
    (2365, 5),
    (7161, 4),
    (7161, 5),
    (7161, 7),
    (7161, 8),
    (6899, 7),
    (6899, 8),
    (7427, 2),
    (7165, 7),
    (7441, 8),
    (7442, 0),
    (7443, 1),
    (7444, 2),
    (7445, 0),
    (7446, 5),
    (7447, 6),
    (7448, 0),
    (7449, 7),
    (7450, 8),
    (7451, 0),
    (7452, 1),
    (7453, 2),
    (7454, 0),
    (7455, 5),
    (7456, 6),
    (7457, 0),
    (7458, 7),
    (7459, 8),
    (7460, 0),
    (7461, 1),
    (7462, 2),
    (7463, 0),
    (7464, 5),
    (7465, 6),
    (7466, 0),
    (7467, 7),
    (7468, 8),
    (7469, 0),
    (7470, 1),
    (7471, 2),
    (7472, 0),
    (7473, 5),
    (7474, 6),
    (7475, 0),
    (7476, 7),
    (7477, 8),
    (7478, 0),
    (7479, 1),
    (7480, 2),
    (7481, 0),
    (7482, 5),
    (7483, 6),
    (7484, 0),
    (7485, 7),
    (7486, 8),
    (7487, 0),
    (7488, 1),
    (7489, 2),
    (7490, 0),
    (7491, 5),
    (7492, 6),
    (7493, 0),
    (7494, 7),
    (7495, 8),
    (7496, 0),
    (7497, 1),
    (7498, 2),
    (7499, 0),
    (7500, 5),
    (7501, 6),
    (7502, 0),
    (7503, 7),
    (7504, 8),
    (7505, 0),
    (7506, 1),
    (7507, 2),
    (7508, 0),
    (7509, 5),
    (7510, 6),
    (7511, 0),
    (7512, 7),
    (7513, 8),
    (7514, 0),
    (7515, 1),
    (7516, 2),
    (7517, 0),
    (7427, 7),
    (7519, 2),
    (7441, 3),
    (7521, 0),
    (7522, 1),
    (7523, 5),
    (7524, 7),
    (7525, 2),
    (7526, 6),
    (7527, 3),
    (7528, 0),
    (7529, 1),
    (7530, 5),
    (7531, 7),
    (7532, 2),
    (7533, 6),
    (7534, 3),
    (7535, 0),
    (7536, 1),
    (7537, 5),
    (7538, 7),
    (7539, 2),
    (7540, 6),
    (7541, 3),
    (7542, 0),
    (7543, 1),
    (7544, 5),
    (7545, 7),
    (7546, 2),
    (7547, 6),
    (7548, 3),
    (7549, 0),
    (7550, 1)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
-- Every nonroot parent is strictly earlier, and every source generator has its actual bound.
/-- Exact chronological parent and source-generator bounds for this whole finite interval. -/
theorem y422TPathRawData58_allowed (j : Fin 128) :
    (7424 + j.val = 0 ∨ (y422TPathRawData58 j).1 < 7424 + j.val) ∧
      (y422TPathRawData58 j).2 < 9 := by
  revert j
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
