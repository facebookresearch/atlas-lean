/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.FundamentalGroupoid.FundamentalGroupIso

/-!
# Compatibility import for the original based homeomorphism API

This public facade reexports `FundamentalGroup.mulEquivOfHomeomorphAt` and
its characteristic lemma from the consolidated fundamental-group
isomorphism API. Its raw carrier universes remain independent.
-/
