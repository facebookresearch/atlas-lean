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
def y422TPathRawData39 : Fin 128 → ℕ × ℕ :=
  ![(4991, 1),
    (4992, 2),
    (4993, 0),
    (4994, 5),
    (4995, 6),
    (4996, 0),
    (4997, 7),
    (4998, 8),
    (4999, 0),
    (5000, 1),
    (5001, 2),
    (5002, 0),
    (5003, 5),
    (5004, 6),
    (5005, 0),
    (5006, 7),
    (5007, 8),
    (5008, 0),
    (5009, 1),
    (5010, 2),
    (5011, 0),
    (2402, 3),
    (5013, 0),
    (5014, 5),
    (5015, 7),
    (5016, 2),
    (5017, 6),
    (5018, 0),
    (5019, 1),
    (5020, 5),
    (5021, 7),
    (5022, 2),
    (5023, 6),
    (5024, 3),
    (5025, 0),
    (5026, 1),
    (5027, 5),
    (5028, 7),
    (5029, 2),
    (5030, 6),
    (5031, 3),
    (5032, 0),
    (5033, 1),
    (5034, 5),
    (5035, 7),
    (5036, 2),
    (5037, 6),
    (5038, 3),
    (5039, 0),
    (5040, 1),
    (5041, 5),
    (5042, 7),
    (5043, 2),
    (5044, 6),
    (5045, 3),
    (5046, 0),
    (5047, 1),
    (5048, 5),
    (5049, 7),
    (5050, 2),
    (5051, 6),
    (5052, 3),
    (5053, 0),
    (5054, 1),
    (5055, 5),
    (5056, 7),
    (5057, 2),
    (5058, 6),
    (5059, 3),
    (5060, 0),
    (5061, 1),
    (5062, 5),
    (5063, 7),
    (5064, 2),
    (5065, 6),
    (5066, 3),
    (5067, 4),
    (5068, 0),
    (5069, 1),
    (5070, 5),
    (5071, 7),
    (5072, 2),
    (5073, 6),
    (5074, 3),
    (5075, 0),
    (5076, 1),
    (5077, 5),
    (5078, 7),
    (5079, 2),
    (5080, 6),
    (5081, 3),
    (5082, 0),
    (5083, 1),
    (5084, 5),
    (5085, 7),
    (5086, 2),
    (5087, 6),
    (5088, 3),
    (5089, 0),
    (5090, 1),
    (5091, 5),
    (5092, 7),
    (5093, 2),
    (5094, 6),
    (5095, 3),
    (5096, 0),
    (5097, 1),
    (5098, 5),
    (5099, 7),
    (5100, 2),
    (5101, 6),
    (5102, 3),
    (5103, 0),
    (5104, 1),
    (5105, 5),
    (5106, 7),
    (5107, 2),
    (5108, 6),
    (5109, 3),
    (5110, 0),
    (5111, 1),
    (5112, 5),
    (5113, 7),
    (5114, 2),
    (5115, 6),
    (5116, 3),
    (5117, 0),
    (5118, 1)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
-- Every nonroot parent is strictly earlier, and every source generator has its actual bound.
/-- Exact chronological parent and source-generator bounds for this whole finite interval. -/
theorem y422TPathRawData39_allowed (j : Fin 128) :
    (4992 + j.val = 0 ∨ (y422TPathRawData39 j).1 < 4992 + j.val) ∧
      (y422TPathRawData39 j).2 < 9 := by
  revert j
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
