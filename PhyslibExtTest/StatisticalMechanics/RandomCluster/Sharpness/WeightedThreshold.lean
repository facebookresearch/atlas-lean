/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.Sharpness.WeightedThreshold

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.Sharpness.WeightedThreshold`

For the homogeneous coupling `J = 1` with one phase on `ℤ²`, `q = 2`, `β₀ = 3`:
* `weightedPhaseSharpConstant_pos`: the sharp constant is positive;
* `weightedPhasePhysical_subcritical_decay_of_threshold` at `β = 1`, `δ = 1/4`, given that `1` is
  below the threshold `β₁`: a positive decay constant exists, with the decay bound;
* `weightedThreshold_eq_selectedPhaseCritical_of_highBetaWitness`, given a high-β witness.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.Sharpness.WeightedThreshold

open _root_.StatMech _root_.StatMech.OSSS
open Lattice FK
open FKSharpnessWeightedPeriodic FKSharpnessWeightedInfiniteVolume
open FKSharpnessWeightedStrict FKSharpnessWeightedIntegration
open FKSharpnessWeightedCoherentLimit
open IntegrationSubcritical BetaThresholdBound
open BetaCMatch LogCesaroLimit FKSharpnessWeightedThreshold

/-- The homogeneous one-phase coupling on `ℤ^d`. -/
def unitJ (d : ℕ) : Unit → Sym2 (Site d) → ℝ := fun _ _ => 1

/-- The homogeneous coupling with one phase is phase-covariant. -/
theorem unit_phaseCovariant (d : ℕ) :
    PhaseCovariant (fun _ : Sym2 (Site d) => (1 : ℝ)) (fun _ => ()) (unitJ d) :=
  fun _ _ => rfl

-- The sharp constant is positive.
example : 0 < weightedPhaseSharpConstant 2 1 1 3 :=
  weightedPhaseSharpConstant_pos 2 one_pos

-- Exponential decay below the threshold: `β = 1`, `δ = 1/4`, `β₀ = 3`, homogeneous coupling.
example (hlt : 1 < beta1 (fun b n => Sig (weightedThresholdPhaseSum 2 (unitJ 2) 1 1 2 3) n b)) :
    ∃ Q : ℝ, 0 < Q :=
  let ⟨Q, hQ, _⟩ := weightedPhasePhysical_subcritical_decay_of_threshold 2 (fun _ => 1) 1 1
    one_pos (fun _ => le_rfl) (fun _ => le_rfl) (fun _ => ()) (unitJ 2) (fun _ => ⟨0, rfl⟩)
    (unit_phaseCovariant 2) 2 (1 / 4) 1 3 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) hlt
  ⟨Q, hQ⟩

-- The decay bound itself, at radius `n ≥ 2`, for the decay constant produced by the theorem.
example (hlt : 1 < beta1 (fun b n => Sig (weightedThresholdPhaseSum 2 (unitJ 2) 1 1 2 3) n b)) :=
  weightedPhasePhysical_subcritical_decay_of_threshold 2 (fun _ => 1) 1 1
    one_pos (fun _ => le_rfl) (fun _ => le_rfl) (fun _ => ()) (unitJ 2) (fun _ => ⟨0, rfl⟩)
    (unit_phaseCovariant 2) 2 (1 / 4) 1 3 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) hlt

-- Threshold = selected critical point, given a high-β witness.
example (hhigh : weightedSelectedPhaseHighBetaWitness 2 (unitJ 2)
      ((unit_phaseCovariant 2).phaseCoupling_pos (fun _ => ⟨0, rfl⟩)
        (fun _ => one_pos.trans_le le_rfl)) 2 (zero_lt_one.trans_le (by norm_num)) 3) :=
  weightedThreshold_eq_selectedPhaseCritical_of_highBetaWitness 2 (fun _ => 1) 1 1 one_pos
    (fun _ => le_rfl) (fun _ => le_rfl) (fun _ => ()) (unitJ 2) (fun _ => ⟨0, rfl⟩)
    (unit_phaseCovariant 2) 2 3 (by norm_num) hhigh ()

end PhyslibExtTest.StatisticalMechanics.RandomCluster.Sharpness.WeightedThreshold
