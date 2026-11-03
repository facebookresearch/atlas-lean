/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.Sharpness.WeightedHighBeta

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.Sharpness.WeightedHighBeta`

For the homogeneous coupling `J = 1` with one phase (`P = Unit`) on `ℤ²`, `q = 2`:
* `PhaseCovariant` holds, so the hypotheses are satisfiable;
* `exists_weightedSelectedPhaseHighBetaWitness_of_two_le` produces a high-β witness;
* `phaseCoupling_lower` transfers the lower bound `1 ≤ J` to the phase couplings;
* `bcProbW_const`: constant weights give the homogeneous boundary-condition measure.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.Sharpness.WeightedHighBeta

open _root_.StatMech _root_.StatMech.OSSS
open FKSharpnessWeightedPeriodic FKSharpnessWeightedHighBeta FKSharpnessWeightedThreshold

/-- The homogeneous coupling with one phase is phase-covariant. -/
theorem unit_phaseCovariant (d : ℕ) :
    PhaseCovariant (fun _ : Sym2 (Lattice.Site d) => (1 : ℝ)) (fun _ => ())
      (fun _ _ => 1) := fun _ _ => rfl

-- A high-β witness exists for the homogeneous coupling on `ℤ²`.
example : ∃ beta0 : ℝ, weightedSelectedPhaseHighBetaWitness 2 (fun (_ : Unit) _ => (1 : ℝ))
    ((unit_phaseCovariant 2).phaseCoupling_pos (fun _ => ⟨0, rfl⟩)
      (fun _ => one_pos.trans_le le_rfl)) 2 (by norm_num) beta0 :=
  exists_weightedSelectedPhaseHighBetaWitness_of_two_le 2 le_rfl (fun _ => 1) 1 one_pos
    (fun _ => le_rfl) (fun _ => ()) (fun _ _ => 1) (fun _ => ⟨0, rfl⟩) (unit_phaseCovariant 2) 2
    (by norm_num)

-- The lower bound on `J` passes to the phase couplings.
example : ∀ (a : Unit) (e : Sym2 (Lattice.Site 2)), (1 : ℝ) ≤ (fun _ _ => (1 : ℝ)) a e :=
  phaseCoupling_lower (unit_phaseCovariant 2) (fun _ => ⟨0, rfl⟩) (fun _ => le_rfl)

-- Constant weights give the homogeneous boundary-condition measure.
example (ω : ConfigSpace (Sym2 (Fin 2))) :
    FK.bcProbW (⊤ : SimpleGraph (Fin 2)) ⊥ (fun _ => 1 / 2) 2 ω
      = FK.bcProb ⊤ ⊥ (1 / 2) 2 ω :=
  FK.bcProbW_const _ _ _ _ ω

end PhyslibExtTest.StatisticalMechanics.RandomCluster.Sharpness.WeightedHighBeta
