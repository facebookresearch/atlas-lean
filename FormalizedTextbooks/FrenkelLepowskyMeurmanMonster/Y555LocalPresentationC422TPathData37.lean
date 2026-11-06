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
def y422TPathRawData37 : Fin 128 → ℕ × ℕ :=
  ![(4735, 8),
    (4736, 0),
    (4737, 1),
    (4738, 2),
    (4739, 0),
    (4740, 5),
    (4741, 6),
    (4742, 0),
    (4743, 7),
    (4744, 8),
    (4745, 0),
    (4746, 1),
    (4747, 2),
    (4748, 0),
    (4749, 5),
    (4750, 6),
    (4751, 0),
    (4752, 7),
    (4753, 8),
    (4754, 0),
    (4755, 1),
    (4756, 2),
    (4757, 0),
    (4758, 5),
    (4759, 6),
    (4760, 0),
    (4761, 7),
    (4762, 8),
    (4706, 5),
    (4707, 3),
    (4765, 0),
    (4766, 1),
    (4767, 2),
    (4768, 3),
    (4769, 0),
    (4770, 1),
    (4771, 5),
    (4772, 7),
    (4773, 2),
    (4774, 6),
    (4775, 3),
    (4776, 0),
    (4777, 1),
    (4778, 5),
    (4779, 7),
    (4780, 2),
    (4781, 6),
    (4782, 3),
    (4783, 0),
    (4784, 1),
    (4785, 5),
    (4786, 7),
    (4787, 2),
    (4788, 6),
    (4789, 3),
    (4790, 0),
    (4791, 1),
    (4792, 5),
    (4793, 7),
    (4794, 2),
    (4795, 6),
    (4796, 3),
    (4797, 0),
    (4798, 1),
    (4799, 5),
    (4800, 7),
    (4801, 2),
    (4802, 6),
    (4803, 3),
    (4804, 0),
    (4805, 1),
    (4806, 5),
    (4807, 7),
    (4808, 2),
    (4809, 6),
    (4810, 3),
    (4811, 4),
    (4812, 0),
    (4813, 1),
    (4814, 5),
    (4815, 7),
    (4816, 2),
    (4817, 6),
    (4818, 3),
    (4819, 0),
    (4820, 1),
    (4821, 5),
    (4822, 7),
    (4823, 2),
    (4824, 6),
    (4825, 3),
    (4826, 0),
    (4827, 1),
    (4828, 5),
    (4829, 7),
    (4830, 2),
    (4831, 6),
    (4832, 3),
    (4833, 0),
    (4834, 1),
    (4835, 5),
    (4836, 7),
    (4837, 2),
    (4838, 6),
    (4839, 3),
    (4840, 0),
    (4841, 1),
    (4842, 5),
    (4843, 7),
    (4844, 2),
    (4845, 6),
    (4846, 3),
    (4847, 0),
    (4848, 1),
    (4849, 5),
    (4850, 7),
    (4851, 2),
    (4852, 6),
    (4853, 3),
    (4854, 0),
    (4855, 1),
    (4856, 5),
    (4857, 7),
    (4858, 2),
    (4859, 6),
    (4860, 3),
    (4861, 0),
    (4862, 1)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
-- Every nonroot parent is strictly earlier, and every source generator has its actual bound.
/-- Exact chronological parent and source-generator bounds for this whole finite interval. -/
theorem y422TPathRawData37_allowed (j : Fin 128) :
    (4736 + j.val = 0 ∨ (y422TPathRawData37 j).1 < 4736 + j.val) ∧
      (y422TPathRawData37 j).2 < 9 := by
  revert j
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
