/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.AlgebraicTopology.SimplicialObject.BisimplicialEilenbergZilber.ShihHomotopy

/-! # Tests for the natural bisimplicial Shih homotopy -/

@[expose] public section

#check AlgebraicTopology.BisimplicialEilenbergZilber.explicitAlternatingShihOperator
#check AlgebraicTopology.BisimplicialEilenbergZilber.explicitAlternatingShihOperator_boundary
#check AlgebraicTopology.BisimplicialEilenbergZilber.AlternatingAlexanderWhitneyShuffleHomotopy
#check AlgebraicTopology.BisimplicialEilenbergZilber.homotopy
#check AlgebraicTopology.BisimplicialEilenbergZilber.homotopy_hom
#check AlgebraicTopology.BisimplicialEilenbergZilber.homotopy_naturality

end
