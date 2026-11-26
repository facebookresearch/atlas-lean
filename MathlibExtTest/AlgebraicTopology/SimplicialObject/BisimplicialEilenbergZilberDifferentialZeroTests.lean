/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.AlgebraicTopology.SimplicialObject.BisimplicialEilenbergZilber.DifferentialZero

/-! # Tests for the zero-boundary bisimplicial shuffle differential -/

@[expose] public section

#check AlgebraicTopology.BisimplicialEilenbergZilber.diagonalBoundaryMapRightZero
#check AlgebraicTopology.BisimplicialEilenbergZilber.shuffleBoundaryTermRightZero
#check AlgebraicTopology.BisimplicialEilenbergZilber.diagonalBoundaryMapRightZero_leftBoundary
#check AlgebraicTopology.BisimplicialEilenbergZilber.shuffleBidegree_comp_objD_right_zero
#check AlgebraicTopology.BisimplicialEilenbergZilber.diagonalBoundaryMapLeftZero
#check AlgebraicTopology.BisimplicialEilenbergZilber.shuffleBoundaryTermLeftZero
#check AlgebraicTopology.BisimplicialEilenbergZilber.diagonalBoundaryMapLeftZero_rightBoundary
#check AlgebraicTopology.BisimplicialEilenbergZilber.shuffleBidegree_comp_objD_left_zero

end
