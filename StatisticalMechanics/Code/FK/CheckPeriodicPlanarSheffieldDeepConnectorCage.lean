/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.FK.PeriodicPlanarSheffieldDeepConnectorCage

open StatMech FK
open StatMech.FK.PeriodicPlanar

#print axioms
  PeriodicPlaneEmbedding.finiteDeepOpenExitedJoinedBoundaryArmEvent_witnesses
#print axioms
  PeriodicPlaneEmbedding.finiteDeepOpenExitedJoinedBoundaryArmEvent_subset_verticalCrossing
#print axioms
  PeriodicPlaneEmbedding.finiteDeepOpenExitedJoinedBoundaryArmEvent_tendsto_one
#print axioms
  PeriodicPlanarDualPair.finiteDeepOpenExitedJoinedBoundaryArmEvent_subset_threeCrossingCageEvent
#print axioms
  PeriodicPlanarDualPair.finiteDeepOpenExitedJoinedBoundaryArmEvent_disjoint_boundaryBand_of_subset_cage
