/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.ULiftFibration

open CategoryTheory HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

universe u v

example {K M : SSet.{u}} (p : K ⟶ M) [Fibration p] :
    Fibration (SSet.uliftFunctor.{v, u}.map p) :=
  SSet.modelCategoryQuillen.uliftFunctor_map_fibration p
