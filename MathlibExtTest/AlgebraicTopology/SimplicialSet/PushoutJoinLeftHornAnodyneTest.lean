/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.PushoutJoinLeftHornAnodyne

/-!
# Tests for pushout joins with left horns
-/

set_option autoImplicit false

open CategoryTheory
open scoped Simplicial

universe u

namespace SSet

example {n : ℕ} (i : Fin (n + 1)) (hi : i < Fin.last n)
    {K₀ K : SSet.{u}} (j : K₀ ⟶ K) [Mono j] :
    innerAnodyneExtensions
      (joinUnderPushoutObjObj j (horn n i).ι).ι :=
  innerAnodyneExtensions_pushoutJoin_leftHorn i hi j

-- The smallest genuine case: `Λ[1,0]` joined with a monomorphism.
example {K₀ K : SSet.{u}} (j : K₀ ⟶ K) [Mono j] :
    innerAnodyneExtensions
      (joinUnderPushoutObjObj j (horn 1 (0 : Fin 2)).ι).ι :=
  innerAnodyneExtensions_pushoutJoin_leftHorn 0 (by decide) j

end SSet
