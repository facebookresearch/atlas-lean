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
def y422TPathRawData40 : Fin 128 → ℕ × ℕ :=
  ![(5119, 5),
    (5120, 7),
    (5121, 2),
    (5122, 6),
    (5123, 3),
    (5124, 0),
    (5125, 1),
    (5126, 5),
    (5127, 7),
    (5128, 2),
    (5129, 6),
    (5130, 3),
    (5131, 4),
    (5132, 0),
    (5133, 1),
    (5134, 5),
    (5135, 7),
    (5136, 2),
    (5137, 6),
    (5138, 3),
    (5139, 0),
    (5140, 1),
    (5141, 5),
    (5142, 7),
    (5143, 2),
    (5144, 6),
    (5145, 3),
    (5146, 0),
    (5147, 1),
    (5148, 5),
    (5149, 7),
    (5150, 2),
    (5151, 6),
    (5152, 3),
    (5153, 0),
    (5154, 1),
    (5155, 5),
    (5156, 7),
    (5157, 2),
    (5158, 6),
    (5159, 3),
    (5160, 0),
    (5161, 1),
    (5162, 5),
    (5163, 7),
    (5164, 2),
    (5165, 6),
    (5166, 3),
    (5167, 0),
    (5168, 1),
    (5169, 5),
    (5170, 7),
    (5171, 2),
    (5172, 6),
    (5173, 3),
    (5174, 0),
    (5175, 1),
    (5176, 5),
    (5177, 7),
    (5178, 2),
    (5179, 6),
    (5180, 3),
    (5181, 0),
    (5182, 1),
    (5183, 5),
    (5184, 7),
    (5185, 2),
    (5186, 6),
    (5187, 3),
    (5188, 0),
    (5189, 1),
    (5190, 5),
    (5191, 7),
    (113, 1),
    (113, 3),
    (3462, 3),
    (5195, 2),
    (3462, 8),
    (4941, 4),
    (4941, 7),
    (4941, 8),
    (4763, 7),
    (5201, 8),
    (5202, 0),
    (5203, 1),
    (5204, 2),
    (5205, 5),
    (5206, 6),
    (5207, 0),
    (5208, 7),
    (5209, 8),
    (5210, 0),
    (5211, 1),
    (5212, 2),
    (5213, 0),
    (5214, 5),
    (5215, 6),
    (5216, 0),
    (5217, 7),
    (5218, 8),
    (5219, 0),
    (5220, 1),
    (5221, 2),
    (5222, 0),
    (5223, 5),
    (5224, 6),
    (5225, 0),
    (5226, 7),
    (5227, 8),
    (5228, 0),
    (5229, 1),
    (5230, 2),
    (5231, 0),
    (5232, 5),
    (5233, 6),
    (5234, 0),
    (5235, 7),
    (5236, 8),
    (5237, 0),
    (5238, 1),
    (5239, 2),
    (5240, 0),
    (5241, 5),
    (5242, 6),
    (5243, 0),
    (5244, 7),
    (5245, 8),
    (5246, 0)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
-- Every nonroot parent is strictly earlier, and every source generator has its actual bound.
/-- Exact chronological parent and source-generator bounds for this whole finite interval. -/
theorem y422TPathRawData40_allowed (j : Fin 128) :
    (5120 + j.val = 0 ∨ (y422TPathRawData40 j).1 < 5120 + j.val) ∧
      (y422TPathRawData40 j).2 < 9 := by
  revert j
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
