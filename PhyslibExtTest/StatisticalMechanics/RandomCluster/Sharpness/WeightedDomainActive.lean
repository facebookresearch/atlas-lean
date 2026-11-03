/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.Sharpness.WeightedDomainActive

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.Sharpness.WeightedDomainActive`

With the identity embedding of a finite graph into itself, equal edge parameters in `(0, 1)`,
`q = 2`, and the increasing event `univ`:
* the embedding hypotheses `ocd_AdjMatch` and `ocd_ParamCompatible` hold;
* `ocd_free_inner_dominated_activeBCMean` applies with free outer boundary;
* `ocd_wired_inner_dominated_activeBCMean` applies with fully wired inner boundary (the wiring
  hypothesis holds);
* the free domination instantiated on `K₂` with parameters `1/2`.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.Sharpness.WeightedDomainActive

open _root_.StatMech _root_.StatMech.FK

/-- The identity embedding of a graph into itself matches adjacency. -/
theorem adjMatch_id {V : Type*} (G : SimpleGraph V) : ocd_AdjMatch G G id := fun _ _ => Iff.rfl

/-- Equal edge parameters are compatible along the identity embedding. -/
theorem paramCompatible_id {V : Type*} (pf : Sym2 V → ℝ) : ocd_ParamCompatible id pf pf := by
  intro e
  simp only [ocd_innerEdge, Sym2.map_id', id_eq]

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

-- Free inner measure is dominated by the outer measure (identity embedding, event \`univ\`).
example (pf : Sym2 V → ℝ) (h0 : ∀ e, 0 < pf e) (h1 : ∀ e, pf e < 1) :
    activeBCMean G ⊥ pf 2 ((Set.univ : Set (ConfigSpace G.edgeSet)).indicator fun _ => 1) ≤
      activeBCMean G (Lattice.boundaryCliqueGraph fun _ => False) pf 2
        (fun rho => (Set.univ : Set (ConfigSpace G.edgeSet)).indicator (fun _ => 1)
          (ocd_innerRestrictActive G G id (adjMatch_id G) rho)) :=
  ocd_free_inner_dominated_activeBCMean G G id (fun _ => False) Function.injective_id
    (adjMatch_id G) (paramCompatible_id pf) h0 h1 h0 h1 (by norm_num) isUpperSet_univ

-- The outer measure is dominated by the fully wired inner measure (identity embedding).
example (pf : Sym2 V → ℝ) (h0 : ∀ e, 0 < pf e) (h1 : ∀ e, pf e < 1) :
    activeBCMean G (Lattice.boundaryCliqueGraph fun _ => False) pf 2
        (fun rho => (Set.univ : Set (ConfigSpace G.edgeSet)).indicator (fun _ => 1)
          (ocd_innerRestrictActive G G id (adjMatch_id G) rho)) ≤
      activeBCMean G (Lattice.boundaryCliqueGraph fun _ => True) pf 2
        ((Set.univ : Set (ConfigSpace G.edgeSet)).indicator fun _ => 1) :=
  ocd_wired_inner_dominated_activeBCMean G G id (fun _ => False) Function.injective_id
    (adjMatch_id G) (fun _ => True) (paramCompatible_id pf) h0 h1 h0 h1 (by norm_num)
    (fun _ x y h => (Lattice.boundaryCliqueGraph_adj _ x y).2 ⟨h.1, trivial, trivial⟩)
    isUpperSet_univ

-- The hypotheses are satisfiable: constant parameters \`1/2\` on \`K₂\` instantiate the first.
example :
    activeBCMean (⊤ : SimpleGraph (Fin 2)) ⊥ (fun _ => 1 / 2) 2
        ((Set.univ : Set (ConfigSpace (⊤ : SimpleGraph (Fin 2)).edgeSet)).indicator
          fun _ => 1) ≤
      activeBCMean (⊤ : SimpleGraph (Fin 2)) (Lattice.boundaryCliqueGraph fun _ => False)
        (fun _ => 1 / 2) 2
        (fun rho => (Set.univ : Set (ConfigSpace (⊤ : SimpleGraph (Fin 2)).edgeSet)).indicator
          (fun _ => 1) (ocd_innerRestrictActive ⊤ ⊤ id (adjMatch_id ⊤) rho)) :=
  ocd_free_inner_dominated_activeBCMean ⊤ ⊤ id (fun _ => False) Function.injective_id
    (adjMatch_id ⊤) (paramCompatible_id _) (fun _ => by norm_num) (fun _ => by norm_num)
    (fun _ => by norm_num) (fun _ => by norm_num) (by norm_num) isUpperSet_univ

end PhyslibExtTest.StatisticalMechanics.RandomCluster.Sharpness.WeightedDomainActive
