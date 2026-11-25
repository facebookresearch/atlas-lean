/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.AlgebraicTopology.SimplicialObject.BisimplicialEilenbergZilber.Normalization

/-! # Tests for double normalization of bisimplicial total complexes -/

@[expose] public section

#check AlgebraicTopology.BisimplicialNormalization.outerPInfty
#check AlgebraicTopology.BisimplicialNormalization.verticalPInfty
#check AlgebraicTopology.BisimplicialNormalization.outerPInfty_comp_verticalPInfty
#check AlgebraicTopology.BisimplicialNormalization.outerTotalHomotopy
#check AlgebraicTopology.BisimplicialNormalization.verticalTotalHomotopy
#check AlgebraicTopology.BisimplicialNormalization.totalPInfty
#check AlgebraicTopology.BisimplicialNormalization.totalPInftyHomotopy
#check AlgebraicTopology.BisimplicialNormalization.bidegreePInfty_idem
#check AlgebraicTopology.BisimplicialNormalization.totalι_comp_totalPInfty

end
