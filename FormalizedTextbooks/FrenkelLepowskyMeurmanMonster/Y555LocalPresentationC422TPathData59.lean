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
def y422TPathRawData59 : Fin 128 → ℕ × ℕ :=
  ![(7551, 5),
    (7552, 7),
    (7553, 2),
    (7554, 6),
    (7555, 3),
    (7556, 0),
    (7557, 1),
    (7558, 5),
    (7559, 7),
    (7560, 2),
    (7561, 6),
    (7562, 3),
    (7563, 0),
    (7564, 1),
    (7565, 5),
    (7566, 7),
    (7567, 2),
    (7568, 6),
    (7569, 3),
    (7570, 0),
    (7571, 1),
    (7572, 5),
    (7573, 7),
    (7574, 2),
    (7575, 6),
    (7576, 3),
    (7577, 4),
    (7578, 0),
    (7579, 1),
    (7580, 5),
    (7581, 7),
    (7582, 2),
    (7583, 6),
    (7584, 3),
    (7585, 0),
    (7586, 1),
    (7587, 5),
    (7588, 7),
    (7589, 2),
    (7590, 6),
    (7591, 3),
    (7592, 0),
    (7593, 1),
    (7594, 5),
    (7595, 7),
    (7596, 2),
    (7597, 6),
    (7598, 3),
    (7599, 0),
    (7600, 1),
    (7601, 5),
    (7602, 7),
    (7603, 2),
    (7604, 6),
    (7605, 3),
    (7606, 0),
    (7607, 1),
    (7608, 5),
    (7609, 7),
    (7610, 2),
    (7611, 6),
    (7612, 3),
    (7613, 0),
    (7614, 1),
    (7615, 5),
    (7616, 7),
    (7617, 2),
    (7618, 6),
    (7619, 3),
    (7620, 0),
    (7621, 1),
    (7622, 5),
    (7623, 7),
    (7624, 2),
    (7625, 6),
    (7626, 3),
    (7627, 0),
    (7628, 1),
    (7629, 5),
    (7630, 7),
    (7631, 2),
    (7632, 6),
    (7633, 3),
    (7634, 0),
    (7635, 1),
    (7636, 5),
    (7637, 7),
    (7638, 2),
    (7639, 6),
    (7640, 3),
    (7641, 4),
    (7642, 0),
    (7643, 1),
    (7644, 5),
    (7645, 7),
    (7646, 2),
    (7647, 6),
    (7648, 3),
    (7649, 0),
    (7650, 1),
    (7651, 5),
    (7652, 7),
    (7653, 2),
    (7654, 6),
    (7655, 3),
    (7656, 0),
    (7657, 1),
    (7658, 5),
    (7659, 7),
    (7660, 2),
    (7661, 6),
    (7662, 3),
    (7663, 0),
    (7664, 1),
    (7665, 5),
    (7666, 7),
    (7667, 2),
    (7668, 6),
    (7669, 3),
    (7670, 0),
    (7671, 1),
    (7672, 5),
    (7673, 7),
    (7674, 2),
    (7675, 6),
    (7676, 3),
    (7677, 0),
    (7678, 1)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
-- Every nonroot parent is strictly earlier, and every source generator has its actual bound.
/-- Exact chronological parent and source-generator bounds for this whole finite interval. -/
theorem y422TPathRawData59_allowed (j : Fin 128) :
    (7552 + j.val = 0 ∨ (y422TPathRawData59 j).1 < 7552 + j.val) ∧
      (y422TPathRawData59 j).2 < 9 := by
  revert j
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
