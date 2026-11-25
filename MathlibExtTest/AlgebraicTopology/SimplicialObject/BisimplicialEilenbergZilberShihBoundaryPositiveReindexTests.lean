/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.AlgebraicTopology.SimplicialObject.BisimplicialEilenbergZilber.ShihBoundaryPositiveReindex

/-! # Tests for bisimplicial Shih positive-face reindexing -/

@[expose] public section

#check AlgebraicTopology.BisimplicialEilenbergZilber.shihPositivePrefixCoordinate_sum_eq_zero
#check AlgebraicTopology.BisimplicialEilenbergZilber.shihPositiveBoundary_sum_eq_residual
#check AlgebraicTopology.BisimplicialEilenbergZilber.shihPositiveBoundary_sum_eq_partitioned
#check AlgebraicTopology.BisimplicialEilenbergZilber.shihPositiveBoundary_sum_eq_reindexed
#check AlgebraicTopology.BisimplicialEilenbergZilber.ShihPositiveFaceIdentity
#check AlgebraicTopology.BisimplicialEilenbergZilber.ShihReindexedPositiveFaceIdentity
#check AlgebraicTopology.BisimplicialEilenbergZilber.shihPositiveFaceIdentity_iff_reindexed

end
