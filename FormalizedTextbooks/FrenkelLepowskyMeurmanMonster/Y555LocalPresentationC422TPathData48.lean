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
def y422TPathRawData48 : Fin 128 → ℕ × ℕ :=
  ![(6143, 7),
    (6144, 2),
    (6145, 6),
    (6146, 3),
    (6147, 0),
    (6148, 1),
    (6149, 5),
    (6150, 7),
    (6151, 2),
    (6152, 6),
    (6153, 3),
    (6154, 0),
    (6155, 1),
    (6156, 5),
    (6157, 7),
    (6158, 2),
    (6159, 6),
    (6160, 3),
    (6161, 0),
    (6162, 1),
    (6163, 5),
    (6164, 7),
    (6165, 2),
    (6166, 6),
    (6167, 3),
    (6168, 0),
    (6169, 1),
    (6170, 5),
    (6171, 7),
    (6172, 2),
    (6173, 6),
    (6174, 3),
    (6175, 0),
    (6176, 1),
    (6177, 5),
    (6178, 7),
    (117, 3),
    (117, 6),
    (3466, 3),
    (1428, 3),
    (3466, 5),
    (3466, 6),
    (5982, 4),
    (5982, 5),
    (5982, 6),
    (730, 3),
    (6189, 0),
    (6190, 1),
    (6191, 5),
    (6192, 7),
    (6193, 2),
    (6194, 6),
    (6195, 3),
    (6196, 0),
    (6197, 1),
    (6198, 5),
    (6199, 7),
    (6200, 2),
    (6201, 6),
    (6202, 3),
    (6203, 0),
    (6204, 1),
    (6205, 5),
    (6206, 7),
    (6207, 2),
    (6208, 6),
    (6209, 3),
    (6210, 0),
    (6211, 1),
    (6212, 5),
    (6213, 7),
    (6214, 2),
    (6215, 6),
    (6216, 3),
    (6217, 0),
    (6218, 1),
    (6219, 5),
    (6220, 7),
    (6221, 2),
    (6222, 6),
    (6223, 3),
    (6224, 0),
    (6225, 1),
    (6226, 5),
    (6227, 7),
    (6228, 2),
    (6229, 6),
    (6230, 3),
    (6231, 0),
    (6232, 1),
    (6233, 5),
    (6234, 7),
    (6235, 2),
    (6236, 6),
    (6237, 3),
    (6238, 0),
    (6239, 1),
    (6240, 5),
    (6241, 7),
    (6242, 2),
    (6243, 6),
    (6244, 3),
    (6245, 4),
    (6246, 0),
    (6247, 1),
    (6248, 5),
    (6249, 7),
    (6250, 2),
    (6251, 6),
    (6252, 3),
    (6253, 0),
    (6254, 1),
    (6255, 5),
    (6256, 7),
    (6257, 2),
    (6258, 6),
    (6259, 3),
    (6260, 0),
    (6261, 1),
    (6262, 5),
    (6263, 7),
    (6264, 2),
    (6265, 6),
    (6266, 3),
    (6267, 0),
    (6268, 1),
    (6269, 5),
    (6270, 7)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
-- Every nonroot parent is strictly earlier, and every source generator has its actual bound.
/-- Exact chronological parent and source-generator bounds for this whole finite interval. -/
theorem y422TPathRawData48_allowed (j : Fin 128) :
    (6144 + j.val = 0 ∨ (y422TPathRawData48 j).1 < 6144 + j.val) ∧
      (y422TPathRawData48 j).2 < 9 := by
  revert j
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
