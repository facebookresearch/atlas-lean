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
def y422TPathRawData45 : Fin 128 → ℕ × ℕ :=
  ![(5759, 0),
    (5760, 1),
    (5761, 2),
    (5762, 0),
    (5763, 5),
    (5764, 6),
    (5765, 0),
    (5766, 7),
    (5767, 8),
    (5768, 0),
    (5769, 1),
    (5770, 2),
    (5771, 0),
    (5772, 5),
    (5773, 6),
    (5774, 0),
    (5775, 7),
    (5776, 8),
    (5777, 0),
    (5778, 1),
    (5779, 2),
    (5780, 0),
    (5781, 5),
    (5782, 6),
    (5783, 0),
    (5784, 7),
    (5785, 8),
    (5786, 0),
    (5787, 1),
    (5788, 2),
    (5789, 0),
    (5790, 5),
    (5791, 6),
    (5792, 0),
    (5793, 7),
    (5794, 8),
    (5795, 0),
    (5796, 1),
    (5797, 2),
    (5798, 0),
    (5799, 5),
    (4269, 7),
    (5801, 2),
    (5802, 3),
    (5803, 0),
    (5804, 1),
    (5805, 5),
    (5806, 7),
    (5807, 2),
    (5808, 6),
    (5809, 3),
    (5810, 0),
    (5811, 1),
    (5812, 5),
    (5813, 7),
    (5814, 2),
    (5815, 6),
    (5816, 3),
    (5817, 0),
    (5818, 1),
    (5819, 5),
    (5820, 7),
    (5821, 2),
    (5822, 6),
    (5823, 3),
    (5824, 0),
    (5825, 1),
    (5826, 5),
    (5827, 7),
    (5828, 2),
    (5829, 6),
    (5830, 3),
    (5831, 0),
    (5832, 1),
    (5833, 5),
    (5834, 7),
    (5835, 2),
    (5836, 6),
    (5837, 3),
    (5838, 0),
    (5839, 1),
    (5840, 5),
    (5841, 7),
    (5842, 2),
    (5843, 6),
    (5844, 3),
    (5845, 0),
    (5846, 1),
    (5847, 5),
    (5848, 7),
    (5849, 2),
    (5850, 6),
    (5851, 3),
    (5852, 0),
    (5853, 1),
    (5854, 5),
    (5855, 7),
    (5856, 2),
    (5857, 6),
    (5858, 3),
    (5859, 4),
    (5860, 0),
    (5861, 1),
    (5862, 5),
    (5863, 7),
    (5864, 2),
    (5865, 6),
    (5866, 3),
    (5867, 0),
    (5868, 1),
    (5869, 5),
    (5870, 7),
    (5871, 2),
    (5872, 6),
    (5873, 3),
    (5874, 0),
    (5875, 1),
    (5876, 5),
    (5877, 7),
    (5878, 2),
    (5879, 6),
    (5880, 3),
    (5881, 0),
    (5882, 1),
    (5883, 5),
    (5884, 7),
    (5885, 2),
    (5886, 6)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
-- Every nonroot parent is strictly earlier, and every source generator has its actual bound.
/-- Exact chronological parent and source-generator bounds for this whole finite interval. -/
theorem y422TPathRawData45_allowed (j : Fin 128) :
    (5760 + j.val = 0 ∨ (y422TPathRawData45 j).1 < 5760 + j.val) ∧
      (y422TPathRawData45 j).2 < 9 := by
  revert j
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
