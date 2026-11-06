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
def y422TPathRawData64 : Fin 128 → ℕ × ℕ :=
  ![(8191, 5),
    (8192, 7),
    (8193, 2),
    (8194, 6),
    (8195, 3),
    (8196, 0),
    (8197, 1),
    (8198, 5),
    (8199, 7),
    (8200, 2),
    (8201, 6),
    (8202, 3),
    (8203, 0),
    (8204, 1),
    (8205, 5),
    (8206, 7),
    (8207, 2),
    (8208, 6),
    (8209, 3),
    (8210, 0),
    (8211, 1),
    (8212, 5),
    (8213, 7),
    (8214, 2),
    (8215, 6),
    (8216, 3),
    (8217, 0),
    (8218, 1),
    (8219, 5),
    (8220, 7),
    (8221, 2),
    (8222, 6),
    (8223, 3),
    (8224, 0),
    (8225, 1),
    (8226, 5),
    (8227, 7),
    (8228, 2),
    (8229, 6),
    (8230, 3),
    (8231, 0),
    (8232, 1),
    (8233, 5),
    (8234, 7),
    (8235, 2),
    (8236, 6),
    (8237, 3),
    (8238, 0),
    (8239, 1),
    (8240, 5),
    (8241, 7),
    (8242, 2),
    (8243, 6),
    (8244, 3),
    (8245, 0),
    (8246, 1),
    (126, 0),
    (8248, 1),
    (125, 3),
    (125, 5),
    (125, 6),
    (7974, 2),
    (322, 2),
    (7974, 3),
    (7974, 6),
    (2368, 3),
    (8257, 2),
    (8258, 3),
    (2368, 6),
    (2368, 7),
    (7980, 4),
    (7980, 6),
    (7980, 7),
    (7982, 5),
    (126, 5),
    (8266, 2),
    (8267, 3),
    (8268, 0),
    (8269, 1),
    (8270, 5),
    (8271, 7),
    (8272, 2),
    (8273, 6),
    (8274, 3),
    (8275, 0),
    (8276, 1),
    (8277, 5),
    (8278, 7),
    (8279, 2),
    (8280, 6),
    (8281, 3),
    (8282, 0),
    (8283, 1),
    (8284, 5),
    (8285, 7),
    (8286, 2),
    (8287, 6),
    (8288, 3),
    (8289, 0),
    (8290, 1),
    (8291, 5),
    (8292, 7),
    (8293, 2),
    (8294, 6),
    (8295, 3),
    (8296, 0),
    (8297, 1),
    (8298, 5),
    (8299, 7),
    (8300, 2),
    (8301, 6),
    (8302, 3),
    (8303, 0),
    (8304, 1),
    (8305, 5),
    (8306, 7),
    (8307, 2),
    (8308, 6),
    (8309, 3),
    (8310, 0),
    (8311, 1),
    (8312, 5),
    (8313, 7),
    (8314, 2),
    (8315, 6),
    (8316, 3),
    (8317, 0),
    (8318, 1)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
-- Every nonroot parent is strictly earlier, and every source generator has its actual bound.
/-- Exact chronological parent and source-generator bounds for this whole finite interval. -/
theorem y422TPathRawData64_allowed (j : Fin 128) :
    (8192 + j.val = 0 ∨ (y422TPathRawData64 j).1 < 8192 + j.val) ∧
      (y422TPathRawData64 j).2 < 9 := by
  revert j
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
