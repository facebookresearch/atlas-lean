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
def y422TPathRawData01 : Fin 128 → ℕ × ℕ :=
  ![(127, 0),
    (128, 5),
    (129, 6),
    (130, 0),
    (131, 7),
    (132, 8),
    (133, 0),
    (134, 1),
    (135, 2),
    (136, 0),
    (137, 5),
    (138, 6),
    (139, 0),
    (140, 7),
    (141, 8),
    (142, 0),
    (143, 1),
    (144, 2),
    (145, 0),
    (146, 5),
    (147, 6),
    (148, 0),
    (149, 7),
    (150, 8),
    (151, 0),
    (43, 0),
    (153, 1),
    (154, 5),
    (155, 7),
    (156, 2),
    (157, 6),
    (158, 3),
    (159, 4),
    (160, 0),
    (161, 1),
    (162, 5),
    (163, 7),
    (164, 2),
    (165, 6),
    (166, 3),
    (167, 0),
    (168, 1),
    (169, 5),
    (170, 7),
    (171, 2),
    (172, 6),
    (173, 3),
    (174, 0),
    (175, 1),
    (176, 5),
    (177, 7),
    (178, 2),
    (179, 6),
    (180, 3),
    (181, 0),
    (182, 1),
    (183, 5),
    (184, 7),
    (185, 2),
    (186, 6),
    (187, 3),
    (188, 0),
    (189, 1),
    (190, 5),
    (191, 7),
    (192, 2),
    (193, 6),
    (194, 3),
    (195, 0),
    (196, 1),
    (197, 5),
    (198, 7),
    (199, 2),
    (200, 6),
    (201, 3),
    (202, 0),
    (203, 1),
    (204, 5),
    (205, 7),
    (206, 2),
    (207, 6),
    (208, 3),
    (209, 0),
    (210, 1),
    (211, 5),
    (212, 7),
    (213, 2),
    (214, 6),
    (215, 3),
    (216, 0),
    (217, 1),
    (218, 5),
    (219, 7),
    (220, 2),
    (221, 6),
    (222, 3),
    (159, 0),
    (224, 1),
    (225, 5),
    (226, 7),
    (227, 2),
    (228, 6),
    (229, 3),
    (230, 4),
    (231, 0),
    (232, 1),
    (233, 5),
    (234, 7),
    (235, 2),
    (236, 6),
    (237, 3),
    (238, 0),
    (239, 1),
    (240, 5),
    (241, 7),
    (242, 2),
    (243, 6),
    (244, 3),
    (245, 0),
    (246, 1),
    (247, 5),
    (248, 7),
    (249, 2),
    (250, 6),
    (251, 3),
    (252, 0),
    (253, 1),
    (254, 5)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
-- Every nonroot parent is strictly earlier, and every source generator has its actual bound.
/-- Exact chronological parent and source-generator bounds for this whole finite interval. -/
theorem y422TPathRawData01_allowed (j : Fin 128) :
    (128 + j.val = 0 ∨ (y422TPathRawData01 j).1 < 128 + j.val) ∧
      (y422TPathRawData01 j).2 < 9 := by
  revert j
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
