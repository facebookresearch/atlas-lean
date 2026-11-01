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
def y422TPathRawData38 : Fin 128 → ℕ × ℕ :=
  ![(4863, 5),
    (4864, 7),
    (4865, 2),
    (4866, 6),
    (4867, 3),
    (4868, 0),
    (4869, 1),
    (4870, 5),
    (4871, 7),
    (4872, 2),
    (4873, 6),
    (4874, 3),
    (4875, 4),
    (4876, 0),
    (4877, 1),
    (4878, 5),
    (4879, 7),
    (4880, 2),
    (4881, 6),
    (4882, 3),
    (4883, 0),
    (4884, 1),
    (4885, 5),
    (4886, 7),
    (4887, 2),
    (4888, 6),
    (4889, 3),
    (4890, 0),
    (4891, 1),
    (4892, 5),
    (4893, 7),
    (4894, 2),
    (4895, 6),
    (4896, 3),
    (4897, 0),
    (4898, 1),
    (4899, 5),
    (4900, 7),
    (4901, 2),
    (4902, 6),
    (4903, 3),
    (4904, 0),
    (4905, 1),
    (4906, 5),
    (4907, 7),
    (4908, 2),
    (4909, 6),
    (4910, 3),
    (4911, 0),
    (4912, 1),
    (4913, 5),
    (4914, 7),
    (4915, 2),
    (4916, 6),
    (4917, 3),
    (4918, 0),
    (4919, 1),
    (4920, 5),
    (4921, 7),
    (4922, 2),
    (4923, 6),
    (4924, 3),
    (4925, 0),
    (4926, 1),
    (4927, 5),
    (4928, 7),
    (4929, 2),
    (4930, 6),
    (4931, 3),
    (4932, 0),
    (4933, 1),
    (4934, 5),
    (4469, 3),
    (4469, 7),
    (1272, 2),
    (4938, 3),
    (4702, 4),
    (4702, 6),
    (4702, 7),
    (4702, 8),
    (4713, 7),
    (4944, 8),
    (4945, 0),
    (4946, 1),
    (4947, 2),
    (4948, 0),
    (4949, 5),
    (4950, 6),
    (4951, 0),
    (4952, 7),
    (4953, 8),
    (4954, 0),
    (4955, 1),
    (4956, 2),
    (4957, 0),
    (4958, 5),
    (4959, 6),
    (4960, 0),
    (4961, 7),
    (4962, 8),
    (4963, 0),
    (4964, 1),
    (4965, 2),
    (4966, 0),
    (4967, 5),
    (4968, 6),
    (4969, 0),
    (4970, 7),
    (4971, 8),
    (4972, 0),
    (4973, 1),
    (4974, 2),
    (4975, 0),
    (4976, 5),
    (4977, 6),
    (4978, 0),
    (4979, 7),
    (4980, 8),
    (4981, 0),
    (4982, 1),
    (4983, 2),
    (4984, 0),
    (4985, 5),
    (4986, 6),
    (4987, 0),
    (4988, 7),
    (4989, 8),
    (4990, 0)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
-- Every nonroot parent is strictly earlier, and every source generator has its actual bound.
/-- Exact chronological parent and source-generator bounds for this whole finite interval. -/
theorem y422TPathRawData38_allowed (j : Fin 128) :
    (4864 + j.val = 0 ∨ (y422TPathRawData38 j).1 < 4864 + j.val) ∧
      (y422TPathRawData38 j).2 < 9 := by
  revert j
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
