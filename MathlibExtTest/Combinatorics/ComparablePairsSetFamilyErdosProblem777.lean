/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.ComparablePairsSetFamilyErdosProblem777

open MathlibExt.Combinatorics.ComparablePairsSetFamilyErdosProblem777Wanted

-- The middle layer on two points is an antichain.
example : comparablePairs ({{0}, {1}} : Finset (Finset (Fin 2))) = 0 := by
  unfold comparablePairs
  decide

-- In the full square there are four cover relations and one further strict containment.
example : comparablePairs (Finset.univ : Finset (Finset (Fin 2))) = 5 := by
  unfold comparablePairs
  decide
