/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.FK.PeriodicPlanarSheffieldWholeArcCrosscut

open StatMech

#print axioms Lattice.halfPlane_walks_intersect
#print axioms Lattice.halfPlane_walks_intersect_of_endpoint_outside
#print axioms ContinuousHalfPlaneCrosscut.wholeArc_intersects_escape
#print axioms ContinuousHalfPlaneCrosscut.wholeArc_intersects_escape_of_far
#print axioms ContinuousHalfPlaneCrosscut.wholeArc_intersects_escape_of_outside

open FK.PeriodicPlanar.PeriodicPlanarDualPair

#print axioms exists_open_graphWalk_to_exposedRectExit
#print axioms WholeArcBoundaryPlacement.toIncidence_of_exposedEndpoint
#print axioms no_open_primal_dual_of_wholeArcBoundaryIncidence
#print axioms no_open_primal_dual_of_wholeArcTraceIncidence
