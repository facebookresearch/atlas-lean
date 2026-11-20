/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.FrontierA.MonotoneAutomatonFiniteMerge

open MeasureTheory
open StatMech Lattice ConfigSpace Percolation FrontierA

#check openSubgraph_siteForce_eq_forceOpen
#check numInfiniteClusters_siteForce_lt_of_twoMeetBox
#check finite_constant_cluster_count_impossible
#check site_cluster_count_ae_lt_two_or_infinite
#check site_cluster_count_ae_one_or_infinite

#print axioms StatMech.FrontierA.openSubgraph_siteForce_eq_forceOpen
#print axioms StatMech.FrontierA.numInfiniteClusters_siteForce_lt_of_twoMeetBox
#print axioms StatMech.FrontierA.finite_constant_cluster_count_impossible
#print axioms StatMech.FrontierA.site_cluster_count_ae_lt_two_or_infinite
#print axioms StatMech.FrontierA.site_cluster_count_ae_one_or_infinite
