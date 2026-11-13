/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Universality.RSWConnectorCentralFaceCarrier










open Finset SimpleGraph Set

namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section



noncomputable def RlcBookFaithfulExtremalTracePair.toSequentialExplorationState
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (hfaith : RlcBookFaithfulExtremalTracePair gamma gamma') :
    RlcSequentialExtremalExplorationState gamma gamma' :=
  RlcSequentialExtremalExplorationState.ofNonempty
    hfaith.extremal_realizable



theorem RlcBookFaithfulExtremalTracePair.sequentialComparison_closed
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (hfaith : RlcBookFaithfulExtremalTracePair gamma gamma')
    {e : Sym2 (Site 2)}
    (he : e ∈ rlc_sequentialExtremalExteriorEdges gamma gamma') :
    rlc_sequentialExtremalClosedComparison gamma gamma'
        hfaith.toSequentialExplorationState.rawConfig e = false :=
  rlc_sequentialExtremalClosedComparison_of_mem _ he



theorem RlcBookFaithfulExtremalTracePair.sequentialComparison_agrees
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (hfaith : RlcBookFaithfulExtremalTracePair gamma gamma')
    {e : Sym2 (Site 2)}
    (he : e ∉ rlc_sequentialExtremalExteriorEdges gamma gamma') :
    rlc_sequentialExtremalClosedComparison gamma gamma'
        hfaith.toSequentialExplorationState.rawConfig e =
      hfaith.toSequentialExplorationState.rawConfig e :=
  rlc_sequentialExtremalClosedComparison_of_not_mem _ he

end

end StatMech.Universality
