/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.AlgebraicTopology.SimplicialObject.BisimplicialEilenbergZilber.ShihComposite

/-! # Tests for the bisimplicial Alexander--Whitney--shuffle composite -/

@[expose] public section

#check AlgebraicTopology.BisimplicialEilenbergZilber.awShuffleDiagonalSummand
#check AlgebraicTopology.BisimplicialEilenbergZilber.awShuffleDiagonalComponent
#check AlgebraicTopology.BisimplicialEilenbergZilber.awShuffleZeroComponent
#check AlgebraicTopology.BisimplicialEilenbergZilber.faceToBidegreeOfEq_eq_map
#check AlgebraicTopology.BisimplicialEilenbergZilber.alternatingMap_comp_f_eq_awShuffleDiagonalComponent

end
