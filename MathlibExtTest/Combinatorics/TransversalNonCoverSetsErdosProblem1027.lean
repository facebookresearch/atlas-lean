/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.TransversalNonCoverSetsErdosProblem1027

open MathlibExt.Combinatorics.TransversalNonCoverSetsErdosProblem1027Wanted

-- The empty family has one coloring, while an empty edge rules out every coloring.
example : transversalNonCoverSets ∅ = {∅} := by decide

example : transversalNonCoverSets {∅} = ∅ := by decide

-- On a two-edge path the middle vertex and the pair of endpoints are the two color classes.
example : transversalNonCoverSets {{0, 1}, {1, 2}} = {{1}, {0, 2}} := by decide
