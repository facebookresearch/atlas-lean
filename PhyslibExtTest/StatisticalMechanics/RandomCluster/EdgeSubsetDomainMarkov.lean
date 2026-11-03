/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.EdgeSubsetDomainMarkov

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.EdgeSubsetDomainMarkov`

On `Fin 2` with `K = H = ⊤` (one edge) and empty wiring `B = ⊥`, at `p = 1/2`, `q = 2`:
* `edgeSubsetFibreConfig_restrictActive` as a `simp` lemma, and `edgeSubsetFibreConfig_agreesOff`;
* `edgeSubsetFibre_condBcProb_eq_activeBCProb`: the conditional law on a fibre is the active law
  with the induced wiring;
* `edgeSubsetFibreCondEventMass_eq_bcEventMass` for the sure event.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.EdgeSubsetDomainMarkov

open _root_.StatMech _root_.StatMech.FK

/-- The one-edge test graph. -/
abbrev G2 : SimpleGraph (Fin 2) := ⊤

-- The fibre configuration restricts back and agrees with `ψ` off `K`.
example (ψ : ConfigSpace (Sym2 (Fin 2))) (η : ConfigSpace G2.edgeSet) :
    restrictActive G2 (edgeSubsetFibreConfig G2 ψ η) = η ∧
      AgreesOff G2.edgeFinset ψ (edgeSubsetFibreConfig G2 ψ η) :=
  ⟨by simp, edgeSubsetFibreConfig_agreesOff G2 ψ η⟩

-- Domain Markov: the conditional law on the fibre is the active law with induced wiring.
example (ψ : ConfigSpace (Sym2 (Fin 2))) (η : ConfigSpace G2.edgeSet) :
    condBcProb G2 ⊥ (1 / 2) 2 G2.edgeFinset ψ (edgeSubsetFibreConfig G2 ψ η) =
      activeBCProb G2 (edgeSubsetInducedWiring G2 G2 ⊥ ψ) (fun _ => 1 / 2) 2 η :=
  edgeSubsetFibre_condBcProb_eq_activeBCProb G2 G2 ⊥ le_rfl ψ (by norm_num) (by norm_num) η

-- The event version, for the sure event.
example (ψ : ConfigSpace (Sym2 (Fin 2))) :
    edgeSubsetFibreCondEventMass G2 G2 ⊥ ψ (1 / 2) 2 Set.univ =
      bcEventMass G2 (edgeSubsetInducedWiring G2 G2 ⊥ ψ) (1 / 2) 2
        (restrictActive G2 ⁻¹' Set.univ) :=
  edgeSubsetFibreCondEventMass_eq_bcEventMass G2 G2 ⊥ le_rfl ψ (by norm_num) (by norm_num)
    (by norm_num) _

end PhyslibExtTest.StatisticalMechanics.RandomCluster.EdgeSubsetDomainMarkov
