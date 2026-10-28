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
def y422TPathRawData06 : Fin 128 → ℕ × ℕ :=
  ![(767, 0),
    (768, 7),
    (769, 8),
    (770, 0),
    (771, 1),
    (772, 2),
    (773, 0),
    (774, 5),
    (775, 6),
    (776, 0),
    (777, 7),
    (778, 8),
    (779, 0),
    (780, 1),
    (781, 2),
    (782, 0),
    (783, 5),
    (362, 7),
    (658, 5),
    (491, 3),
    (17, 2),
    (570, 6),
    (716, 0),
    (491, 8),
    (718, 7),
    (106, 1),
    (793, 0),
    (794, 5),
    (795, 6),
    (796, 7),
    (797, 0),
    (798, 1),
    (799, 2),
    (800, 0),
    (801, 5),
    (802, 6),
    (803, 0),
    (804, 7),
    (805, 8),
    (806, 0),
    (807, 1),
    (808, 2),
    (809, 0),
    (810, 5),
    (811, 6),
    (812, 0),
    (813, 7),
    (814, 8),
    (815, 0),
    (816, 1),
    (817, 2),
    (818, 0),
    (819, 5),
    (820, 6),
    (821, 0),
    (822, 7),
    (823, 8),
    (824, 0),
    (825, 1),
    (826, 2),
    (827, 0),
    (828, 5),
    (829, 6),
    (830, 0),
    (831, 7),
    (832, 8),
    (833, 0),
    (834, 1),
    (835, 2),
    (836, 0),
    (837, 5),
    (838, 6),
    (839, 0),
    (840, 7),
    (841, 8),
    (842, 0),
    (15, 8),
    (632, 1),
    (845, 2),
    (846, 5),
    (847, 6),
    (848, 0),
    (849, 7),
    (850, 8),
    (851, 0),
    (852, 1),
    (853, 2),
    (854, 0),
    (855, 5),
    (856, 6),
    (857, 0),
    (858, 7),
    (859, 8),
    (860, 0),
    (861, 1),
    (862, 2),
    (863, 0),
    (864, 5),
    (865, 6),
    (866, 0),
    (867, 7),
    (868, 8),
    (869, 0),
    (870, 1),
    (871, 2),
    (872, 0),
    (873, 5),
    (874, 6),
    (875, 0),
    (876, 7),
    (877, 8),
    (878, 0),
    (879, 1),
    (880, 2),
    (881, 0),
    (882, 5),
    (883, 6),
    (884, 0),
    (885, 7),
    (886, 8),
    (887, 0),
    (888, 1),
    (889, 2),
    (890, 0),
    (891, 5),
    (892, 6),
    (893, 0),
    (894, 7)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
-- Every nonroot parent is strictly earlier, and every source generator has its actual bound.
/-- Exact chronological parent and source-generator bounds for this whole finite interval. -/
theorem y422TPathRawData06_allowed (j : Fin 128) :
    (768 + j.val = 0 ∨ (y422TPathRawData06 j).1 < 768 + j.val) ∧
      (y422TPathRawData06 j).2 < 9 := by
  revert j
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
