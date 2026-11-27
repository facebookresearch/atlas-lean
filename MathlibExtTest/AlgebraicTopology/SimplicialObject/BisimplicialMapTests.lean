/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.AlgebraicTopology.SimplicialObject.BisimplicialMap

/-! # Tests for maps in two simplicial directions -/

@[expose] public section

#check AlgebraicTopology.Bisimplicial.map
#check AlgebraicTopology.Bisimplicial.map_eq_inner_outer
#check AlgebraicTopology.Bisimplicial.map_comp
#check AlgebraicTopology.Bisimplicial.map_id
#check AlgebraicTopology.Bisimplicial.map_delta_id
#check AlgebraicTopology.Bisimplicial.map_id_delta
#check AlgebraicTopology.Bisimplicial.map_eqToHom
#check AlgebraicTopology.Bisimplicial.map_diagonal
#check AlgebraicTopology.Bisimplicial.map_naturality

end
