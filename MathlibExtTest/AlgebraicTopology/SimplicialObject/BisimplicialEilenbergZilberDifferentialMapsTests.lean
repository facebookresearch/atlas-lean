/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.AlgebraicTopology.SimplicialObject.BisimplicialEilenbergZilber.DifferentialMaps

/-! # Tests for bisimplicial shuffle boundary maps -/

@[expose] public section

#check AlgebraicTopology.BisimplicialEilenbergZilber.diagonalBoundaryMapPositive
#check AlgebraicTopology.BisimplicialEilenbergZilber.diagonalBoundaryMapPositive_eq_map
#check AlgebraicTopology.BisimplicialEilenbergZilber.diagonalBoundaryMapPositive_partner
#check AlgebraicTopology.BisimplicialEilenbergZilber.shuffleBoundaryTermPositive
#check AlgebraicTopology.BisimplicialEilenbergZilber.shuffleBoundaryTermPositive_partner
#check AlgebraicTopology.BisimplicialEilenbergZilber.diagonalBoundaryMapPositive_leftBoundary
#check AlgebraicTopology.BisimplicialEilenbergZilber.diagonalBoundaryMapPositive_rightBoundary
#check AlgebraicTopology.BisimplicialEilenbergZilber.shuffleBoundaryTermPositive_leftBoundary
#check AlgebraicTopology.BisimplicialEilenbergZilber.shuffleBoundaryTermPositive_rightBoundary

end
