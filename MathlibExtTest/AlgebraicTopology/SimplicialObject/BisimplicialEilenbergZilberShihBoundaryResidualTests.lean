/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.AlgebraicTopology.SimplicialObject.BisimplicialEilenbergZilber.ShihBoundaryResidual

/-! # Tests for the bisimplicial Shih residual identity -/

@[expose] public section

#check AlgebraicTopology.BisimplicialEilenbergZilber.transitionSum_add_leftZeroSum_eq_zero
#check AlgebraicTopology.BisimplicialEilenbergZilber.shihIdentitySurvivor_eq_neg_id
#check AlgebraicTopology.BisimplicialEilenbergZilber.shihLeftEdge_sum_eq_awShuffleZeroComponent_sub_id
#check AlgebraicTopology.BisimplicialEilenbergZilber.shihReindexedPositiveFaceIdentity_of_activeUpperReindex
#check AlgebraicTopology.BisimplicialEilenbergZilber.shihPositiveFaceIdentity

end
