/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/










import Code.FrontierA.KacWardAcyclicElimination
import Code.Onsager.TrivalentCycles

open scoped BigOperators

namespace StatMech.FrontierA

open Finset SimpleGraph
open StatMech.Ising

universe u v



theorem kw_cycleWeight_factor_of_disjoint_partition
    {V : Type u} [DecidableEq V] {R : Type v} [CommMonoid R]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (F : Finset (Sym2 V)) (piece : ι -> Finset (Sym2 V))
    (weight : Sym2 V -> R)
    (hcover : F = Finset.univ.biUnion piece)
    (hdisj : ((Finset.univ : Finset ι) : Set ι).PairwiseDisjoint piece) :
    (∏ edge ∈ F, weight edge) =
      ∏ i, ∏ edge ∈ piece i, weight edge := by
  rw [hcover]
  exact Finset.prod_biUnion hdisj





theorem kw_trivalent_even_cycle_weight_decomposition
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hdeg : ∀ vertex, G.degree vertex ≤ 3)
    (F : Finset (Sym2 V)) (hF : F ∈ evenSubgraphs G)
    {R : Type v} [CommMonoid R] (weight : Sym2 V -> R) :
    ∃ (ι : Type u) (_ : Fintype ι) (_ : DecidableEq ι)
      (base : ι -> V) (cycle : (i : ι) -> G.Walk (base i) (base i)),
      (∀ i, (cycle i).IsCycle) ∧
      F = Finset.univ.biUnion (fun i => (cycle i).edges.toFinset) ∧
      ((Finset.univ : Finset ι) : Set ι).PairwiseDisjoint
        (fun i => (cycle i).edges.toFinset) ∧
      ((Finset.univ : Finset ι) : Set ι).PairwiseDisjoint
        (fun i => (cycle i).toSubgraph.verts) ∧
      (∏ edge ∈ F, weight edge) =
        ∏ i, ∏ edge ∈ (cycle i).edges.toFinset, weight edge := by
  classical
  obtain ⟨ι, finiteι, decidableEqι, base, cycle, hcycle, hcover,
      hedgeDisjoint, hvertexDisjoint⟩ :=
    StatMech.Onsager.ons_trivalent_even_cycle_decomposition G hdeg F hF
  letI : Fintype ι := finiteι
  letI : DecidableEq ι := decidableEqι
  refine ⟨ι, finiteι, decidableEqι, base, cycle, hcycle, hcover,
    hedgeDisjoint, hvertexDisjoint, ?_⟩
  exact kw_cycleWeight_factor_of_disjoint_partition F
    (fun i => (cycle i).edges.toFinset) weight hcover hedgeDisjoint

end StatMech.FrontierA
