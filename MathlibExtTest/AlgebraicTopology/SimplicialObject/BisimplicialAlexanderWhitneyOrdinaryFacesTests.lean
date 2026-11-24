/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.AlgebraicTopology.SimplicialObject.BisimplicialAlexanderWhitney.OrdinaryFaces

/-! # Tests for bisimplicial Alexander--Whitney ordinary faces -/

@[expose] public section

open CategoryTheory Simplicial
open scoped Simplicial

#check AlgebraicTopology.BisimplicialAlexanderWhitney.horizontal_ordinary_face_eq
#check AlgebraicTopology.BisimplicialAlexanderWhitney.vertical_ordinary_face_eq

end
