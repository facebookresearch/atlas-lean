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
def y422TPathRawData00 : Fin 128 → ℕ × ℕ :=
  ![(0, 0),
    (0, 4),
    (1, 3),
    (2, 2),
    (3, 1),
    (4, 0),
    (5, 5),
    (6, 7),
    (7, 6),
    (8, 0),
    (9, 1),
    (10, 5),
    (11, 7),
    (12, 2),
    (13, 6),
    (14, 3),
    (15, 0),
    (16, 1),
    (17, 5),
    (18, 7),
    (19, 2),
    (20, 6),
    (21, 3),
    (22, 0),
    (23, 1),
    (24, 5),
    (25, 7),
    (26, 2),
    (27, 6),
    (28, 3),
    (29, 0),
    (30, 1),
    (31, 5),
    (32, 7),
    (33, 2),
    (34, 6),
    (35, 3),
    (36, 0),
    (37, 1),
    (38, 5),
    (39, 7),
    (40, 2),
    (41, 6),
    (42, 3),
    (43, 4),
    (44, 0),
    (45, 1),
    (46, 5),
    (47, 7),
    (48, 2),
    (49, 6),
    (50, 3),
    (51, 0),
    (52, 1),
    (53, 5),
    (54, 7),
    (55, 2),
    (56, 6),
    (57, 3),
    (58, 0),
    (59, 1),
    (60, 5),
    (61, 7),
    (62, 2),
    (63, 6),
    (64, 3),
    (65, 0),
    (66, 1),
    (67, 5),
    (68, 7),
    (69, 2),
    (70, 6),
    (71, 3),
    (72, 0),
    (73, 1),
    (74, 5),
    (75, 7),
    (76, 2),
    (77, 6),
    (78, 3),
    (79, 0),
    (80, 1),
    (81, 5),
    (82, 7),
    (83, 2),
    (84, 6),
    (85, 3),
    (86, 0),
    (87, 1),
    (88, 5),
    (89, 7),
    (90, 2),
    (91, 6),
    (92, 3),
    (93, 0),
    (94, 1),
    (95, 5),
    (6, 6),
    (8, 8),
    (98, 0),
    (99, 1),
    (100, 2),
    (101, 5),
    (102, 6),
    (103, 0),
    (104, 7),
    (105, 8),
    (106, 0),
    (107, 1),
    (108, 2),
    (109, 0),
    (110, 5),
    (111, 6),
    (112, 0),
    (113, 7),
    (114, 8),
    (115, 0),
    (116, 1),
    (117, 2),
    (118, 0),
    (119, 5),
    (120, 6),
    (121, 0),
    (122, 7),
    (123, 8),
    (124, 0),
    (125, 1),
    (126, 2)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
-- Every nonroot parent is strictly earlier, and every source generator has its actual bound.
/-- Exact chronological parent and source-generator bounds for this whole finite interval. -/
theorem y422TPathRawData00_allowed (j : Fin 128) :
    (0 + j.val = 0 ∨ (y422TPathRawData00 j).1 < 0 + j.val) ∧
      (y422TPathRawData00 j).2 < 9 := by
  revert j
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
