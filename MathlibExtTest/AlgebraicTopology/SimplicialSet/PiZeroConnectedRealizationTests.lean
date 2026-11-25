/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

module

import MathlibExt.AlgebraicTopology.SimplicialSet.PiZeroConnectedRealization

/-!
# Path-connected realization consumer test

Focused downstream check for the public `SSet.pathConnectedSpace_realization_of_isConnected`
API: simplicial connectedness (`X.IsConnected`) supplies path-connectedness
(`PathConnectedSpace`) of the geometric realization.

This is path connectedness only, not contractibility. It establishes no injectivity,
no equivalence, no additivity, no K-space construction, and no `π₀ = K₀` claim.
-/

set_option autoImplicit false

namespace MathlibExtTest.AlgebraicTopology.SimplicialSet.PiZeroConnectedRealizationTests

universe u

/-- Simplicially connected realization is path-connected. Catches signature drift. -/
example (X : SSet.{u}) [X.IsConnected] :
    PathConnectedSpace ↑(SSet.toTop.obj X) :=
  SSet.pathConnectedSpace_realization_of_isConnected X

end MathlibExtTest.AlgebraicTopology.SimplicialSet.PiZeroConnectedRealizationTests
