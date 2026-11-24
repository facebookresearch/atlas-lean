/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.AlgebraicTopology.SimplicialObject.BisimplicialEilenbergZilber.ShihBoundaryFrontReduction

/-! # Tests for the bisimplicial Shih front-face reduction -/

@[expose] public section

#check AlgebraicTopology.BisimplicialEilenbergZilber.gapOneBaseSummand
#check AlgebraicTopology.BisimplicialEilenbergZilber.shihBoundaryTerm_succ_zero_add_lower_zero
#check AlgebraicTopology.BisimplicialEilenbergZilber.sum_upper_gap_gt_one_zero_add_sum_lower_zero
#check AlgebraicTopology.BisimplicialEilenbergZilber.shihUpperBoundaryTerm_zero_of_gap_eq_one
#check AlgebraicTopology.BisimplicialEilenbergZilber.sum_gapOneBaseSummand_eq_awShuffle_sub_zero
#check AlgebraicTopology.BisimplicialEilenbergZilber.shihBoundary_sum_reduction

end
