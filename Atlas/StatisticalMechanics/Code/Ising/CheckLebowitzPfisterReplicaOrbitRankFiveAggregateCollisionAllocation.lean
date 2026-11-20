/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Ising.LebowitzPfisterReplicaOrbitRankFiveAggregateCollisionAllocation

open StatMech.Ising

#print axioms lpReplicaLowRow_parallelInactive_exists_maskFourTarget
#print axioms
  lpReplicaLowRowCollisionParallelData_inactiveSlotPair_eq_complement
#print axioms
  lpReplicaLowRowCrossTraceOutput_collision_maskFour_card_ge_three
#print axioms
  lpReplicaOffdiagLowOrResolvableHighCrossTraceFiberRankFive_card_le_target
#print axioms
  lpReplicaOffdiagLowOrResolvableHighCrossTraceFiberRankFiveEmbedding
#print axioms
  lpReplicaOffdiagLowOrResolvableHighSourcesRankFive_card_le_target
#print axioms
  card_lpReplicaAggregateLowOrResolvableHighSourceRankFive_le_target
#print axioms lpReplicaAggregateLowOrResolvableHighRankFiveEmbedding
