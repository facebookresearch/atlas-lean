/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.AlgebraicTopology.SimplicialObject.BisimplicialEilenbergZilber.Shuffle

/-! # Tests for bisimplicial shuffle components -/

@[expose] public section

#check AlgebraicTopology.BisimplicialEilenbergZilber.shuffleMap
#check AlgebraicTopology.BisimplicialEilenbergZilber.shuffleSummand
#check AlgebraicTopology.BisimplicialEilenbergZilber.shuffleBidegree
#check AlgebraicTopology.BisimplicialEilenbergZilber.shuffleMap_naturality
#check AlgebraicTopology.BisimplicialEilenbergZilber.shuffleSummand_naturality
#check AlgebraicTopology.BisimplicialEilenbergZilber.shuffleBidegree_naturality
#check AlgebraicTopology.BisimplicialEilenbergZilber.component
#check AlgebraicTopology.BisimplicialEilenbergZilber.totalι_comp_component
#check AlgebraicTopology.BisimplicialEilenbergZilber.component_naturality

end
