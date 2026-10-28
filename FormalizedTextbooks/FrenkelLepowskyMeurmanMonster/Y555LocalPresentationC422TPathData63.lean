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
def y422TPathRawData63 : Fin 128 → ℕ × ℕ :=
  ![(8063, 5),
    (7968, 5),
    (8065, 7),
    (8066, 2),
    (8067, 3),
    (8068, 0),
    (8069, 1),
    (8070, 5),
    (8071, 7),
    (8072, 2),
    (8073, 6),
    (8074, 3),
    (8075, 0),
    (8076, 1),
    (8077, 5),
    (8078, 7),
    (8079, 2),
    (8080, 6),
    (8081, 3),
    (8082, 0),
    (8083, 1),
    (8084, 5),
    (8085, 7),
    (8086, 2),
    (8087, 6),
    (8088, 3),
    (8089, 0),
    (8090, 1),
    (8091, 5),
    (8092, 7),
    (8093, 2),
    (8094, 6),
    (8095, 3),
    (8096, 0),
    (8097, 1),
    (8098, 5),
    (8099, 7),
    (8100, 2),
    (8101, 6),
    (8102, 3),
    (8103, 0),
    (8104, 1),
    (8105, 5),
    (8106, 7),
    (8107, 2),
    (8108, 6),
    (8109, 3),
    (8110, 0),
    (8111, 1),
    (8112, 5),
    (8113, 7),
    (8114, 2),
    (8115, 6),
    (8116, 3),
    (8117, 0),
    (8118, 1),
    (8119, 5),
    (8120, 7),
    (8121, 2),
    (8122, 6),
    (8123, 3),
    (8124, 4),
    (8125, 0),
    (8126, 1),
    (8127, 5),
    (8128, 7),
    (8129, 2),
    (8130, 6),
    (8131, 3),
    (8132, 0),
    (8133, 1),
    (8134, 5),
    (8135, 7),
    (8136, 2),
    (8137, 6),
    (8138, 3),
    (8139, 0),
    (8140, 1),
    (8141, 5),
    (8142, 7),
    (8143, 2),
    (8144, 6),
    (8145, 3),
    (8146, 0),
    (8147, 1),
    (8148, 5),
    (8149, 7),
    (8150, 2),
    (8151, 6),
    (8152, 3),
    (8153, 0),
    (8154, 1),
    (8155, 5),
    (8156, 7),
    (8157, 2),
    (8158, 6),
    (8159, 3),
    (8160, 0),
    (8161, 1),
    (8162, 5),
    (8163, 7),
    (8164, 2),
    (8165, 6),
    (8166, 3),
    (8167, 0),
    (8168, 1),
    (8169, 5),
    (8170, 7),
    (8171, 2),
    (8172, 6),
    (8173, 3),
    (8174, 0),
    (8175, 1),
    (8176, 5),
    (8177, 7),
    (8178, 2),
    (8179, 6),
    (8180, 3),
    (8181, 0),
    (8182, 1),
    (8183, 5),
    (8184, 7),
    (8185, 2),
    (8186, 6),
    (8187, 3),
    (8188, 4),
    (8189, 0),
    (8190, 1)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
-- Every nonroot parent is strictly earlier, and every source generator has its actual bound.
/-- Exact chronological parent and source-generator bounds for this whole finite interval. -/
theorem y422TPathRawData63_allowed (j : Fin 128) :
    (8064 + j.val = 0 ∨ (y422TPathRawData63 j).1 < 8064 + j.val) ∧
      (y422TPathRawData63 j).2 < 9 := by
  revert j
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
