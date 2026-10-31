/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.CircuitLowerBound

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.CircuitLowerBound`

On the one-edge graph `⊤` on `Fin 2` at `p = 1/2`, `q = 1`:
* `closeAllOn_of_mem` as a `simp` lemma;
* `closedMass_empty`: the empty closed event has mass `1`;
* `cFE_pow_le_closedEventMass` for `γ = univ`;
* `cFE_pow_le_condClosedOn` conditionally on the all-open configuration.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.CircuitLowerBound

open _root_.StatMech _root_.StatMech.FK

/-- The one-edge test graph. -/
abbrev G2 : SimpleGraph (Fin 2) := ⊤

-- Closing a set of edges closes each of its edges.
example (γ : Finset (Sym2 (Fin 2))) (e : Sym2 (Fin 2)) (he : e ∈ γ)
    (ψ : ConfigSpace (Sym2 (Fin 2))) : closeAllOn γ ψ e = false := by
  simp [he]

-- The empty closed event has mass one.
example : closedMass G2 (1 / 2) 1 ∅ = 1 :=
  closedMass_empty G2 (by norm_num) (by norm_num) (by norm_num)

-- Finite-energy lower bound for closing every edge.
example : cFE (1 / 2) 1 ^ (Finset.univ : Finset (Sym2 (Fin 2))).card ≤
    ∑ ω, (closedEvent Finset.univ).indicator (fun _ => (1 : ℝ)) ω * fkProb G2 (1 / 2) 1 ω :=
  cFE_pow_le_closedEventMass G2 (by norm_num) (by norm_num) le_rfl _

-- The conditional version, given the all-open configuration off `γ`.
example (γ : Finset (Sym2 (Fin 2))) :
    cFE (1 / 2) 1 ^ γ.card ≤
      fkWeight G2 (1 / 2) 1 (closeAllOn γ fun _ => true) /
        agreeWeightSum G2 (1 / 2) 1 γ fun _ => true :=
  cFE_pow_le_condClosedOn G2 (by norm_num) (by norm_num) le_rfl γ _

end PhyslibExtTest.StatisticalMechanics.RandomCluster.CircuitLowerBound
