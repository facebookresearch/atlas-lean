/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.FK.PeriodicPlanarSheffieldExclusion

set_option linter.style.longLine false

#print axioms StatMech.FK.PeriodicPlanar.PeriodicGraph.fourShiftTemplate
#print axioms StatMech.FK.PeriodicPlanar.PeriodicGraph.image_subset_fourShiftTemplate
#print axioms StatMech.FK.PeriodicPlanar.PeriodicGraph.image_right_subset_fourShiftTemplate
#print axioms StatMech.FK.PeriodicPlanar.PeriodicGraph.image_bottom_subset_fourShiftTemplate
#print axioms StatMech.FK.PeriodicPlanar.PeriodicGraph.image_top_subset_fourShiftTemplate
#print axioms
  StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.fourShiftTemplate_preferenceGrid_subset_rect
#print axioms
  StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.preferenceGrid_orbitBox_subset_rect_of_coordinateBound
#print axioms
  StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.rectBottomConnection_fourShiftTemplate_le
#print axioms
  StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.rectLeftConnection_fourShiftTemplate_le
#print axioms
  StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.rectRightConnection_fourShiftTemplate_le
#print axioms
  StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.rectTopConnection_fourShiftTemplate_le
#print axioms
  StatMech.FK.PeriodicPlanar.PeriodicGraph.fourShiftTemplate_hitsInfinite_tendsto_one
#print axioms
  StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.rectSideConnectionEvent_mono_source
#print axioms StatMech.FK.PeriodicPlanar.isFKG_decreasing
#print axioms StatMech.FK.PeriodicPlanar.dualConfigEquiv_antitone
#print axioms
  StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair.dualMeasure_isFKG
#print axioms
  StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair.primalUnique_measure_eq_one_of_common
#print axioms
  StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair.dualUnique_measure_eq_one_of_common
#print axioms
  StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair.freeBufferedInfiniteVolume_sheffieldData_of_common
#print axioms
  StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.exists_uniformTemplate_boundaryLimits_crossing_max_tendsto_one
#print axioms
  StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.exists_fourShiftTemplate_crossing_max_tendsto_one_of_connector
#print axioms
  StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.exists_fourShiftTemplate_crossing_max_tendsto_one_of_coordinateBounds
#print axioms
  StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.exists_commonSquare_fourShift_crossing_max_tendsto_one_of_coordinateBounds
#print axioms
  StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair.freeBufferedInfiniteVolume_commonUnique_measure_zero_or_one
#print axioms
  StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair.freeBufferedInfiniteVolume_commonUnique_measure_eq_zero_iff_ne_one
