/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.CondensedMatter.IsingModel.TwoReplicaWeighted

/-!
# Tests for `PhyslibExt.CondensedMatter.IsingModel.TwoReplicaWeighted`

* `sources_edgeFinset_eq`: the two `sources` APIs agree, checked on the single edge
  `⊤ : SimpleGraph (Fin 2)`.
* `ising_switching_weighted` on the single edge with the unit current `m`, arbitrary `β`,
  couplings `J` and factor `F`, and `A = ∅`: the connectivity hypothesis holds, so the weighted
  sums with sources `{0, 1}` and with no sources agree.
-/

@[expose] public section

namespace PhyslibExtTest.CondensedMatter.IsingModel.TwoReplicaWeighted

open _root_.StatMech _root_.StatMech.Ising
open scoped symmDiff

/-- The single edge, the complete graph on two vertices. -/
abbrev edge : SimpleGraph (Fin 2) := ⊤

/-- One unit of current on every pair. -/
def one : Current (Fin 2) := fun _ => 1

-- The `Ising` and `Sharpness` source sets agree.
example : Ising.sources edge.edgeFinset one = Sharpness.sources edge one :=
  sources_edgeFinset_eq edge one

/-- The odd edges of the unit current connect `0` to `1`. -/
lemma connP_one : connP (oddEdges edge.edgeFinset one) 0 1 := by
  refine Relation.ReflTransGen.single ⟨s(0, 1), ?_, by simp, by simp, by decide⟩
  simp [oddEdges, one]

-- The weighted switching lemma on the single edge.
example (β F : ℝ) (J : Sym2 (Fin 2) → ℝ) :
    splitWeightedSum edge β J one F (∅ ∆ {0, 1}) = splitWeightedSum edge β J one F ∅ :=
  ising_switching_weighted edge β J one (by decide) connP_one F ∅

end PhyslibExtTest.CondensedMatter.IsingModel.TwoReplicaWeighted
