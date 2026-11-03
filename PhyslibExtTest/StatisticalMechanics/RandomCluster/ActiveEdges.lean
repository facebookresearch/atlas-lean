/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.ActiveEdges

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.ActiveEdges`

On the one-edge graph `⊤` on `Fin 2`, with constant edge parameter `1/2` and `q = 2`:
* `extendActive_apply` as a `simp` lemma;
* `active_openMarginal_le_param`: the edge is open with probability at most `1/2`;
* `active_prod_closed_param_le` for `S = univ`;
* `closedProd_antitone` and `prod_one_sub_openMarginal_le_closedProd` applied to the active
  measure (with its FKG lattice condition from `activeProb_FKGLatticeCondition`).
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.ActiveEdges

open _root_.StatMech _root_.StatMech.FK

/-- The one-edge test graph. -/
abbrev G2 : SimpleGraph (Fin 2) := ⊤

/-- The constant edge parameter `1/2`. -/
noncomputable abbrev ph : Sym2 (Fin 2) → ℝ := fun _ => 1 / 2

-- Extensions agree with the active configuration on active edges.
example (ω : ConfigSpace G2.edgeSet) (e : G2.edgeSet) : extendActive G2 ω e.1 = ω e := by
  simp

-- Each edge is open with probability at most its parameter.
example (e : G2.edgeSet) : openMarginal (activeProb G2 ph 2) e ≤ 1 / 2 :=
  active_openMarginal_le_param G2 (fun _ => by norm_num) (fun _ => by norm_num) (by norm_num) e

-- The product of closed parameters bounds the all-closed probability.
example : (∏ _e ∈ (Finset.univ : Finset G2.edgeSet), (1 - (1 / 2 : ℝ))) ≤
    ∑ ω, activeProb G2 ph 2 ω * closedProd Finset.univ ω :=
  active_prod_closed_param_le (pf := ph) G2 (fun _ => by norm_num) (fun _ => by norm_num)
    (by norm_num) Finset.univ

-- The FKG closed-product bound for the active measure, and antitonicity of `closedProd`.
example : (∏ e ∈ (Finset.univ : Finset G2.edgeSet), (1 - openMarginal (activeProb G2 ph 2) e)) ≤
      ∑ ω, activeProb G2 ph 2 ω * closedProd Finset.univ ω ∧
    Antitone (closedProd (Finset.univ : Finset G2.edgeSet)) :=
  ⟨prod_one_sub_openMarginal_le_closedProd _
    (fun ω => (activeProb_pos G2 (fun _ => by norm_num) (fun _ => by norm_num)
      (by norm_num) ω).le)
    (activeProb_sum_eq_one G2 (fun _ => by norm_num) (fun _ => by norm_num) (by norm_num))
    (activeProb_FKGLatticeCondition G2 (fun _ => by norm_num) (fun _ => by norm_num)
      (by norm_num)) _,
   closedProd_antitone _⟩

end PhyslibExtTest.StatisticalMechanics.RandomCluster.ActiveEdges
