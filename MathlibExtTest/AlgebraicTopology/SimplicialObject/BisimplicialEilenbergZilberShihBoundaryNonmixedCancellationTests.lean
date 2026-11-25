/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.AlgebraicTopology.SimplicialObject.BisimplicialEilenbergZilber.ShihBoundaryNonmixedCancellation

/-! # Tests for nonmixed bisimplicial Shih boundary cancellation -/

@[expose] public section

#check AlgebraicTopology.BisimplicialEilenbergZilber.shihLeftBoundaryTerm_add_lower_eq_zero
#check AlgebraicTopology.BisimplicialEilenbergZilber.shihRightBoundaryTerm_add_lower_eq_zero
#check AlgebraicTopology.BisimplicialEilenbergZilber.shihLeftBoundaryInterior_sum_eq_zero
#check AlgebraicTopology.BisimplicialEilenbergZilber.shihRightBoundaryPositive_sum_eq_zero
#check AlgebraicTopology.BisimplicialEilenbergZilber.shihTransitionBoundaryTerm_add_leftZero_eq_zero
#check AlgebraicTopology.BisimplicialEilenbergZilber.shihLeftLastBoundaryTerm_add_rightZero_eq_zero
#check AlgebraicTopology.BisimplicialEilenbergZilber.shihLeftEdge_last_add_zeroSucc_eq_zero

end
