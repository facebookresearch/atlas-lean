/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.PlanarGraphPrismHamiltonicity

/-! The declared conjecture and its refutation use exactly the public graph predicates. -/

open MathlibExt.Combinatorics.PlanarGraphPrismHamiltonicityWanted

example : conjecture =
    (∀ (V : Type) (_ : Fintype V) (_ : DecidableEq V)
      (G : SimpleGraph V) (_ : DecidableRel G.Adj),
      SimpleGraph.IsVertexConnected 3 G → SimpleGraph.IsPlanar G →
        (G □ SimpleGraph.completeGraph (Fin 2)).IsHamiltonian) := rfl

example : ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V)
    (G : SimpleGraph V) (_ : DecidableRel G.Adj),
    SimpleGraph.IsVertexConnected 3 G ∧ SimpleGraph.IsPlanar G ∧
      ¬(G □ SimpleGraph.completeGraph (Fin 2)).IsHamiltonian := by
  classical
  by_contra h
  apply conjecture_refuted
  intro V hF hD G hG hconn hplanar
  by_contra hpris
  exact h ⟨V, hF, hD, G, hG, hconn, hplanar, hpris⟩
