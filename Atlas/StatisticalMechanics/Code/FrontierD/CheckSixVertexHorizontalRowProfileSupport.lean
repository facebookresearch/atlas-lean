/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.FrontierD.SixVertexHorizontalRowProfileSupport

open StatMech.FrontierD

#print axioms sum_sixVertexHorizontalRowZeroCount
#print axioms sum_sixVertexHorizontalPairRowZeroProfile
#print axioms sixVertexHorizontalRowZeroCount_reflect
#print axioms sixVertexSwitchHorizontalPair_rowZeroProfile
#print axioms sixVertexReflectFirstHorizontalLayer_rowZeroProfile
#print axioms sixVertexReflectSecondHorizontalLayer_rowZeroProfile
#print axioms sixVertexSwapHorizontalLayers_rowZeroProfile
#check SixVertexHorizontalRowProfileResidualCapacity
#print axioms actualDeficitTokenHall_rowProfile_iff_capacity
#print axioms configurationBigradeFibers_of_rowProfileResidualHall
#print axioms configurationBigradeFibers_of_rowProfileResidualCapacity
