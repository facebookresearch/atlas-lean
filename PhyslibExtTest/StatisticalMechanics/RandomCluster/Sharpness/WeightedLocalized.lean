/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.Sharpness.WeightedLocalized

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.Sharpness.WeightedLocalized`

* `weightedLocalizedTheta_nonneg`, `weightedLocalizedTheta_le_one`: the localized crossing
  probability lies in `[0, 1]` (unit couplings on `ℤ²`, `q = 2`, `β = 1`);
* `weighted_outer_inner_differential_phaseEnvelope_uniform` applied to the homogeneous one-phase
  coupling at radius `1`;
* `weighted_outer_inner_hcov`: the covariance lower bound, given its revealment-sum hypothesis.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.Sharpness.WeightedLocalized

open _root_.StatMech _root_.StatMech.OSSS
open Lattice FK RevealmentConstruction RevealmentTranslation
open AdaptiveCovLowerGeom LocalizedCrossTree DecisionTree
open WiredBoxDifferential WiredBoxLocalized
open ActiveBoundaryDifferential LindebergTree RussoPrefactor
open FKSharpnessWeightedPeriodic FKSharpnessWeightedPeriodicRepair
open FKSharpnessWeightedStrict FKSharpnessWeightedLocalized

/-- The homogeneous one-phase coupling on `ℤ^d`. -/
def unitJ (d : ℕ) : Unit → Sym2 (Site d) → ℝ := fun _ _ => 1

/-- The homogeneous coupling with one phase is phase-covariant. -/
theorem unit_phaseCovariant (d : ℕ) :
    PhaseCovariant (fun _ : Sym2 (Site d) => (1 : ℝ)) (fun _ => ()) (unitJ d) :=
  fun _ _ => rfl

-- The localized crossing probability lies in `[0, 1]` (unit couplings, `q = 2`, `β = 1`).
example : 0 ≤ weightedLocalizedTheta 2 1 (fun _ => 1) 2 1 ∧
    weightedLocalizedTheta 2 1 (fun _ => 1) 2 1 ≤ 1 :=
  ⟨weightedLocalizedTheta_nonneg 2 1 _ (fun _ => one_pos) 2 1 (by norm_num) one_pos,
    weightedLocalizedTheta_le_one 2 1 _ (fun _ => one_pos) 2 1 (by norm_num) one_pos⟩

-- The uniform differential inequality on the homogeneous one-phase model at radius `1`.
example : 1 * (weightedLocalizedTheta 2 1 (fun _ => 1) 2 1 *
      (1 - weightedLocalizedTheta 2 1 (fun _ => 1) 2 1) /
        (8 * weightedPhaseEnvelopeSig 2 1 (unitJ 2) 2 1 / ((1 : ℕ) : ℝ))) ≤
    deriv (fun b => activeBCMean (boxGraph 2 (2 * 1)) (wiredBoxBoundaryGraph 2 (2 * 1))
      (betaParams (boxCoupling (fun _ => 1) (2 * 1)) b) 2 (innerCrossInd 2 1)) 1 :=
  weighted_outer_inner_differential_phaseEnvelope_uniform 2 1 le_rfl (fun _ => 1) 1 one_pos
    (fun _ => le_rfl) (fun _ => ()) (unitJ 2) (fun _ => ⟨0, rfl⟩) (unit_phaseCovariant 2) 2 1
    (by norm_num) one_pos

-- The covariance lower bound, given the revealment-sum hypothesis.
example (d n : ℕ) (hn : 1 ≤ n) (J : Sym2 (Site d) → ℝ) (hJ : ∀ e, 0 < J e) (D : ℝ) (hD : 0 < D)
    (hsum : ∀ i : (boxGraph d n).edgeSet,
      (∑ k : ↑(Finset.Icc 1 n), localizedBoxReveal
        (activeBCProb (boxGraph d (2 * n)) (wiredBoxBoundaryGraph d (2 * n))
          (betaParams (boxCoupling J (2 * n)) 1) 2)
        (boxActiveEdgeLE d (n_le_two_mul n)) (boxActiveEdge d n) (boxActiveEndU d n)
        (boxActiveEndV d n) (k : ℕ) i) ≤ (Fintype.card (↑(Finset.Icc 1 n)) : ℝ) * D) :
    weightedLocalizedTheta d n J 2 1 * (1 - weightedLocalizedTheta d n J 2 1) / D ≤
      ∑ e, Lindeberg.cov (activeBCProb (boxGraph d (2 * n)) (wiredBoxBoundaryGraph d (2 * n))
          (betaParams (boxCoupling J (2 * n)) 1) 2) (innerCrossInd d n) (Lindeberg.coord e) :=
  weighted_outer_inner_hcov d n hn J hJ 2 1 D (by norm_num) one_pos hD hsum

end PhyslibExtTest.StatisticalMechanics.RandomCluster.Sharpness.WeightedLocalized
