/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.ActiveBoundaryEdges

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.ActiveBoundaryEdges`

On the complete graph `⊤` on `Fin 2` (one edge), with empty wiring `⊥`, constant edge parameter
`1/2` and `q = 2`:
* `activeBCProb_sum_eq_one`: the active measure is a probability mass function;
* `activeBCProb_FKGLatticeCondition`: it satisfies the FKG lattice condition;
* `activeBC_prod_closed_param_le` with `S = univ`;
* `hasDerivAt_activeBCProbOf_beta_sum` (Russo in `β`) at `J = 1`, `β = 1`, `q = 2`.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.ActiveBoundaryEdges

open _root_.StatMech _root_.StatMech.FK

/-- The one-edge test graph. -/
abbrev G2 : SimpleGraph (Fin 2) := ⊤

-- The active measure sums to one.
example : ∑ ω, activeBCProb G2 ⊥ (fun _ => (1 / 2 : ℝ)) 2 ω = 1 :=
  activeBCProb_sum_eq_one G2 ⊥ (fun _ => by norm_num) (fun _ => by norm_num) (by norm_num)

-- The FKG lattice condition holds for `q = 2`.
example : FKGLatticeCondition (activeBCProb G2 ⊥ (fun _ => (1 / 2 : ℝ)) 2) :=
  activeBCProb_FKGLatticeCondition G2 ⊥ (fun _ => by norm_num) (fun _ => by norm_num)
    (by norm_num)

-- The product of closed parameters bounds the all-closed probability.
example : (Finset.univ : Finset G2.edgeSet).prod (fun _ => 1 - (1 / 2 : ℝ)) ≤
    ∑ ω, activeBCProb G2 ⊥ (fun _ => (1 / 2 : ℝ)) 2 ω * closedProd Finset.univ ω :=
  activeBC_prod_closed_param_le (pf := fun _ => 1 / 2) (q := 2) G2 ⊥
    (fun _ => by norm_num) (fun _ => by norm_num)
    (by norm_num) Finset.univ

-- Russo's formula in `β` at `J = 1`, `β = 1`, for the sure event.
example : HasDerivAt (fun b => activeBCProbOf G2 ⊥ (betaParams (fun _ => 1) b) 2 Set.univ)
    (∑ e : G2.edgeSet, ((1 : ℝ) / (1 - Real.exp (-(1 * 1)))) *
      activeBCCov G2 ⊥ (betaParams (fun _ => 1) 1) 2
        (Set.univ.indicator fun _ => (1 : ℝ)) (OSSS.Lindeberg.coord e)) 1 :=
  hasDerivAt_activeBCProbOf_beta_sum G2 ⊥ (fun _ => one_pos) one_pos (by norm_num) Set.univ

end PhyslibExtTest.StatisticalMechanics.RandomCluster.ActiveBoundaryEdges
