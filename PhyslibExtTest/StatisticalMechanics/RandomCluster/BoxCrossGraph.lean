/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.StatisticalMechanics.RandomCluster.BoxCrossGraph

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BoxCrossGraph`

On the boxes `Λ_1 ⊆ Λ_2` of `ℤ²`, at `p = 1/2`, `q = 2`:
* `boxVertIncl` and `innerEdge` are injective, and `crossExt` extends a configuration of `Λ_1` to
  `Λ_2` (it restricts back along `innerEdge`, and agrees with the all-closed configuration off
  the inner edges);
* the headline `condBcProb_crossExt_eq_wiredFkProb` (domain Markov property for the wired box
  measure) at these parameters, and its consequence: the conditional masses of the extended
  configurations sum to `1`.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BoxCrossGraph

open _root_.StatMech _root_.StatMech.FK _root_.StatMech.Lattice

-- The inclusion `Λ_1 → Λ_2` and the induced edge map are injective.
example : Function.Injective (boxVertIncl 2 1) ∧ Function.Injective (innerEdge 2 1) :=
  ⟨boxVertIncl_injective 2 1, innerEdge_injective 2 1⟩

-- `crossExt` restricts back along `innerEdge`.
example (ω : ConfigSpace (Sym2 (boxVerts 2 1))) (e : Sym2 (boxVerts 2 1)) :
    crossExt 2 1 ω (innerEdge 2 1 e) = ω e :=
  crossExt_innerEdge 2 1 ω e

-- `crossExt ω` agrees with the all-closed configuration off the inner edges.
example (ω : ConfigSpace (Sym2 (boxVerts 2 1))) :
    AgreesOff (innerEdgeFinset 2 1) (fun _ => false) (crossExt 2 1 ω) :=
  agreesOff_crossExt 2 1 ω

-- The headline at `d = 2`, `n = 1`, `p = 1/2`, `q = 2`.
example (ω : ConfigSpace (Sym2 (boxVerts 2 1))) :
    condBcProb (boxGraph 2 2) (boundaryCliqueGraph (innerBdry 2 1)) (1 / 2) 2
        (innerEdgeFinset 2 1) (fun _ => false) (crossExt 2 1 ω)
      = wiredFkProb (boxGraph 2 1) (boxBoundary 2 1) (1 / 2) 2 ω :=
  condBcProb_crossExt_eq_wiredFkProb 2 1 (by norm_num) (by norm_num) (by norm_num) ω

-- Consequence: the conditional masses of the extended configurations sum to one.
example : ∑ ω : ConfigSpace (Sym2 (boxVerts 2 1)),
    condBcProb (boxGraph 2 2) (boundaryCliqueGraph (innerBdry 2 1)) (1 / 2) 2
        (innerEdgeFinset 2 1) (fun _ => false) (crossExt 2 1 ω) = 1 := by
  simp only [condBcProb_crossExt_eq_wiredFkProb 2 1 (p := 1 / 2) (q := 2) (by norm_num)
    (by norm_num) (by norm_num)]
  exact wiredFkProb_sum_eq_one _ _ (by norm_num) (by norm_num) (by norm_num)

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BoxCrossGraph
