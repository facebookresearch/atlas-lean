/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.FrontierA.NearestSetGeometry

open Set
open StatMech Lattice FrontierA

#check exists_pair_setL1Distance
#check nearestSourceSet_nonempty
#check nearestSourceFinset_nonempty
#check mem_nearestSourceSet_of_mem_finset
#check l1dist_translate
#check realizedL1Distances_translate
#check setL1Distance_translate
#check nearestSourceSet_translate
#check nearestSourceFinset_translate

#print axioms StatMech.FrontierA.exists_pair_setL1Distance
#print axioms StatMech.FrontierA.nearestSourceFinset_nonempty
#print axioms StatMech.FrontierA.l1dist_translate
#print axioms StatMech.FrontierA.nearestSourceSet_translate
#print axioms StatMech.FrontierA.nearestSourceFinset_translate
