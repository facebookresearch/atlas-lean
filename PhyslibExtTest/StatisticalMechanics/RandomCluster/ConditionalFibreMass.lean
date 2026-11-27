/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.ConditionalFibreMass

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.ConditionalFibreMass`

On the one-edge graph `⊤` on `Fin 2` with empty wiring, at `p = 1/2`, `q = 2`:
* `condBcProb_event_fibre_eq_mass_mul_cond` for the empty and the full conditioning set, and the
  event "the edge `s(0, 1)` is open".
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.ConditionalFibreMass

open _root_.StatMech _root_.StatMech.FK

/-- The one-edge test graph. -/
abbrev G2 : SimpleGraph (Fin 2) := ⊤

/-- The event "the edge `s(0, 1)` is open". -/
def edgeOpen : Set (ConfigSpace (Sym2 (Fin 2))) := {ω | ω s(0, 1) = true}

-- Total probability for the fibre of a configuration over the empty set.
example (ψ : ConfigSpace (Sym2 (Fin 2))) :
    (∑ ρ ∈ condFibre ∅ ψ, edgeOpen.indicator (fun _ => (1 : ℝ)) ρ * bcProb G2 ⊥ (1 / 2) 2 ρ) =
      (∑ σ ∈ condFibre ∅ ψ, bcProb G2 ⊥ (1 / 2) 2 σ) *
        (∑ ρ, edgeOpen.indicator (fun _ => (1 : ℝ)) ρ * condBcProb G2 ⊥ (1 / 2) 2 ∅ ψ ρ) :=
  condBcProb_event_fibre_eq_mass_mul_cond G2 ⊥ (by norm_num) (by norm_num) (by norm_num) _ _ _

-- Total probability for the fibre over all edges.
example (ψ : ConfigSpace (Sym2 (Fin 2))) :
    (∑ ρ ∈ condFibre Finset.univ ψ,
        edgeOpen.indicator (fun _ => (1 : ℝ)) ρ * bcProb G2 ⊥ (1 / 2) 2 ρ) =
      (∑ σ ∈ condFibre Finset.univ ψ, bcProb G2 ⊥ (1 / 2) 2 σ) *
        (∑ ρ, edgeOpen.indicator (fun _ => (1 : ℝ)) ρ *
          condBcProb G2 ⊥ (1 / 2) 2 Finset.univ ψ ρ) :=
  condBcProb_event_fibre_eq_mass_mul_cond G2 ⊥ (by norm_num) (by norm_num) (by norm_num) _ _ _

end PhyslibExtTest.StatisticalMechanics.RandomCluster.ConditionalFibreMass
