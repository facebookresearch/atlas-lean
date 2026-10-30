/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.CornerBalanceUnprobedSite
public import Mathlib

/-!
# Tests for `MathlibExt.Combinatorics.SimpleGraph.Lattice.CornerBalanceUnprobedSite`

* The refutations `not_balancePreservingContraction` and `not_bpc_BalanceSaturatingContraction`,
  and their witness `bpc_holeRing_cornerBalance` (the hole orbit of the four neighbours of the
  origin has positive corner balance). No test assumes either contraction property.
-/

@[expose] public section

open StatMech StatMech.Lattice

namespace MathlibExtTest.StatMech.Combinatorics.SimpleGraph.Lattice.CornerBalanceUnprobedSite

example : ¬ BalancePreservingContraction := not_balancePreservingContraction

example : ¬ bpc_BalanceSaturatingContraction := not_bpc_BalanceSaturatingContraction

example : 0 < cornerBalance bpc_holeRing bpc_holeBase := bpc_holeRing_cornerBalance

end MathlibExtTest.StatMech.Combinatorics.SimpleGraph.Lattice.CornerBalanceUnprobedSite
