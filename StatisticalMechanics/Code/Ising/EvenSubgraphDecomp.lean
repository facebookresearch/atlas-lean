/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/





































import Code.Ising.KWClosedWalkParity

open scoped BigOperators
open Finset SimpleGraph

namespace StatMech

namespace Ising

namespace EvenSubgraphDecomp















variable {V : Type*} [Fintype V] [DecidableEq V]

set_option linter.unusedDecidableInType false in







theorem core_exists_closed_eulerian (G : SimpleGraph V) [DecidableRel G.Adj]
    (hconn : G.Connected) (heven : ∀ x, Even (G.degree x)) (u : V) :
    ∃ p : G.Walk u u, p.IsTrail ∧ ∀ e ∈ G.edgeFinset, e ∈ p.edges :=
  StatMech.Lattice.EulerianExistence.exists_closed_eulerian G hconn heven u











theorem subgraphF_degree_even (F : Finset (Sym2 V)) (hF : ∀ e ∈ F, ¬ e.IsDiag)
    (hev : IsEvenSubgraph F) (v : V) : Even ((subgraphF F).degree v) :=
  subgraphF_even F hF hev v

end EvenSubgraphDecomp




















section Decomp

variable {V : Type} [Fintype V] [DecidableEq V]











theorem evenSubgraphWalkDecomp (Gd : SimpleGraph V) [DecidableRel Gd.Adj] :
    EvenSubgraphWalkDecomp Gd :=
  evenSubgraphWalkDecomp_general Gd

end Decomp

end Ising

end StatMech
