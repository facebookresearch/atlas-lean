/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: Babak Modami
-/
module

public import MathlibExt.Topology.MetricSpace.MinkowskiDimension

@[expose] public section

namespace MathlibExtTest.Topology.MetricSpace.MinkowskiDimension

open MetaMathlibExt

-- Analysis 415: Upper Minkowski dimension

lemma upperMinkowskiDim_nonneg (X : Type) [MetricSpace X] (E : Set X) :
  0 ≤ upperMinkowskiDim X E := zero_le

-- Analysis 416: Lower Minkowski dimension

lemma lowerMinkowskiDim_nonneg (X : Type) [MetricSpace X] (E : Set X) :
  0 ≤ lowerMinkowskiDim X E := zero_le

end MathlibExtTest.Topology.MetricSpace.MinkowskiDimension

end
