/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.FK.TriHexFKCriticalSurface

open StatMech.FK.PeriodicPlanar

#print axioms hexagonalGraph_connected
#print axioms PeriodicGraph.clusterInfinite_pos_of_clusterInfinite_pos
#print axioms PeriodicGraph.clusterInfinite_real_pos_iff
#print axioms triHexPlanarTriBuffered_outerTriangle_dominated
#print axioms triHexPlanarTriBuffered_outerEvent_subset_triangleRestrict
#print axioms triHexPlanarFiniteTriangle_outerEvent_subset_triBufferedRestrict
#print axioms triHexPlanarTriBuffered_mass_le_triangle
#print axioms triHexPlanarFiniteTriangle_le_triBuffered_mass
#print axioms triHexPlanarTriBuffered_eventMass_tendsto
#print axioms triHexPlanar_fixedRootInfinite_real_eq
#print axioms triHexSurfacePercolationEquivalence_of_finiteWiredSweep
#print axioms triHexSurfaceCandidate_criticalPoints_weaklyAligned
#print axioms triangular_hexagonal_critical_of_finiteWiredSweep
