/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Digraph.FiniteDAG
public import Domains.Biology.PopulationGenetics.AdmixtureGraph

/-! The parent digraph of an admixture graph. -/

@[expose] public section

open Digraph

namespace MathlibExtTest.Combinatorics.FiniteDAG

/-- Integration with Atlas: the parent digraph of an admixture graph (edges parent → child) is
acyclic, via `isAcyclic_iff_wellFounded` and the structure's well-foundedness field. -/
example {W : Type*} [Finite W] (A : MathlibExt.Biology.PopulationGenetics.AdmixtureGraph W) :
    (⟨fun Y X => Y ∈ A.parents X⟩ : Digraph W).IsAcyclic :=
  isAcyclic_iff_wellFounded.mpr A.wf

end MathlibExtTest.Combinatorics.FiniteDAG
