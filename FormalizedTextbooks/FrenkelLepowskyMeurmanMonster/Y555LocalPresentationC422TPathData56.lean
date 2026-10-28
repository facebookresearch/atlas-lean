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
def y422TPathRawData56 : Fin 128 → ℕ × ℕ :=
  ![(7167, 7),
    (7168, 8),
    (7169, 0),
    (7170, 1),
    (2319, 5),
    (7172, 6),
    (7173, 0),
    (7174, 7),
    (7175, 8),
    (7176, 0),
    (7177, 1),
    (7178, 2),
    (7179, 0),
    (7180, 5),
    (7181, 6),
    (7182, 0),
    (7183, 7),
    (7184, 8),
    (7185, 0),
    (7186, 1),
    (7187, 2),
    (7188, 0),
    (7189, 5),
    (7190, 6),
    (7191, 0),
    (7192, 7),
    (7193, 8),
    (7194, 0),
    (7195, 1),
    (7196, 2),
    (7197, 0),
    (7198, 5),
    (7199, 6),
    (7200, 0),
    (7201, 7),
    (7202, 8),
    (7203, 0),
    (7204, 1),
    (7205, 2),
    (7206, 0),
    (7207, 5),
    (7208, 6),
    (7209, 0),
    (7210, 7),
    (7211, 8),
    (7212, 0),
    (7213, 1),
    (7214, 2),
    (7215, 0),
    (7216, 5),
    (7217, 6),
    (7218, 0),
    (7219, 7),
    (7220, 8),
    (7221, 0),
    (7222, 1),
    (7223, 2),
    (7224, 0),
    (7225, 5),
    (7226, 6),
    (7227, 0),
    (7228, 7),
    (7229, 8),
    (7230, 0),
    (7231, 1),
    (7232, 2),
    (7233, 0),
    (7234, 5),
    (7235, 6),
    (7236, 0),
    (7237, 7),
    (7238, 8),
    (7239, 0),
    (7240, 1),
    (2503, 5),
    (7242, 7),
    (7243, 2),
    (7244, 3),
    (7245, 0),
    (7246, 1),
    (7247, 5),
    (7248, 7),
    (7249, 2),
    (7250, 6),
    (7251, 3),
    (7252, 0),
    (7253, 1),
    (7254, 5),
    (7255, 7),
    (7256, 2),
    (7257, 6),
    (7258, 3),
    (7259, 0),
    (7260, 1),
    (7261, 5),
    (7262, 7),
    (7263, 2),
    (7264, 6),
    (7265, 3),
    (7266, 0),
    (7267, 1),
    (7268, 5),
    (7269, 7),
    (7270, 2),
    (7271, 6),
    (7272, 3),
    (7273, 0),
    (7274, 1),
    (7275, 5),
    (7276, 7),
    (7277, 2),
    (7278, 6),
    (7279, 3),
    (7280, 0),
    (7281, 1),
    (7282, 5),
    (7283, 7),
    (7284, 2),
    (7285, 6),
    (7286, 3),
    (7287, 0),
    (7288, 1),
    (7289, 5),
    (7290, 7),
    (7291, 2),
    (7292, 6),
    (7293, 3),
    (7294, 0)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
-- Every nonroot parent is strictly earlier, and every source generator has its actual bound.
/-- Exact chronological parent and source-generator bounds for this whole finite interval. -/
theorem y422TPathRawData56_allowed (j : Fin 128) :
    (7168 + j.val = 0 ∨ (y422TPathRawData56 j).1 < 7168 + j.val) ∧
      (y422TPathRawData56 j).2 < 9 := by
  revert j
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
