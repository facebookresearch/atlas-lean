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
def y422TPathRawData57 : Fin 128 → ℕ × ℕ :=
  ![(7295, 1),
    (7296, 5),
    (7297, 7),
    (7298, 2),
    (7299, 6),
    (7300, 3),
    (7301, 4),
    (7302, 0),
    (7303, 1),
    (7304, 5),
    (7305, 7),
    (7306, 2),
    (7307, 6),
    (7308, 3),
    (7309, 0),
    (7310, 1),
    (7311, 5),
    (7312, 7),
    (7313, 2),
    (7314, 6),
    (7315, 3),
    (7316, 0),
    (7317, 1),
    (7318, 5),
    (7319, 7),
    (7320, 2),
    (7321, 6),
    (7322, 3),
    (7323, 0),
    (7324, 1),
    (7325, 5),
    (7326, 7),
    (7327, 2),
    (7328, 6),
    (7329, 3),
    (7330, 0),
    (7331, 1),
    (7332, 5),
    (7333, 7),
    (7334, 2),
    (7335, 6),
    (7336, 3),
    (7337, 0),
    (7338, 1),
    (7339, 5),
    (7340, 7),
    (7341, 2),
    (7342, 6),
    (7343, 3),
    (7344, 0),
    (7345, 1),
    (7346, 5),
    (7347, 7),
    (7348, 2),
    (7349, 6),
    (7350, 3),
    (7351, 0),
    (7352, 1),
    (7353, 5),
    (7354, 7),
    (7355, 2),
    (7356, 6),
    (7357, 3),
    (7358, 0),
    (7359, 1),
    (7360, 5),
    (7361, 7),
    (7362, 2),
    (7363, 6),
    (7364, 3),
    (7365, 4),
    (7366, 0),
    (7367, 1),
    (7368, 5),
    (7369, 7),
    (7370, 2),
    (7371, 6),
    (7372, 3),
    (7373, 0),
    (7374, 1),
    (7375, 5),
    (7376, 7),
    (7377, 2),
    (7378, 6),
    (7379, 3),
    (7380, 0),
    (7381, 1),
    (7382, 5),
    (7383, 7),
    (7384, 2),
    (7385, 6),
    (7386, 3),
    (7387, 0),
    (7388, 1),
    (7389, 5),
    (7390, 7),
    (7391, 2),
    (7392, 6),
    (7393, 3),
    (7394, 0),
    (7395, 1),
    (7396, 5),
    (7397, 7),
    (7398, 2),
    (7399, 6),
    (7400, 3),
    (7401, 0),
    (7402, 1),
    (7403, 5),
    (7404, 7),
    (7405, 2),
    (7406, 6),
    (7407, 3),
    (7408, 0),
    (7409, 1),
    (7410, 5),
    (7411, 7),
    (7412, 2),
    (7413, 6),
    (7414, 3),
    (7415, 0),
    (7416, 1),
    (7417, 5),
    (7418, 7),
    (7419, 2),
    (7420, 6),
    (7421, 3),
    (7422, 0)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
-- Every nonroot parent is strictly earlier, and every source generator has its actual bound.
/-- Exact chronological parent and source-generator bounds for this whole finite interval. -/
theorem y422TPathRawData57_allowed (j : Fin 128) :
    (7296 + j.val = 0 ∨ (y422TPathRawData57 j).1 < 7296 + j.val) ∧
      (y422TPathRawData57 j).2 < 9 := by
  revert j
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
