/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.AlgebraicTopology.SimplicialObject.BisimplicialAlexanderWhitney.Reindexing

/-! # Tests for bisimplicial Alexander--Whitney ordinary-face reindexing -/

@[expose] public section

#check AlgebraicTopology.BisimplicialAlexanderWhitney.horizontalOrdinaryTerm
#check AlgebraicTopology.BisimplicialAlexanderWhitney.verticalOrdinaryTerm
#check AlgebraicTopology.BisimplicialAlexanderWhitney.diagonalOrdinaryTerm
#check AlgebraicTopology.BisimplicialAlexanderWhitney.horizontalOrdinaryTerm_eq_diagonal
#check AlgebraicTopology.BisimplicialAlexanderWhitney.verticalOrdinaryTerm_eq_diagonal
#check AlgebraicTopology.BisimplicialAlexanderWhitney.ordinaryTerms_eq_diagonalDoubleSum

end
