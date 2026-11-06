/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsPairingCriterion
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LocalInvariance

/-! Whole actual vector pairings from complete finite short packets and physical coordinates. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators

/-- A complete sparse short packet gives a finite formula for the entire actual Griess pairing. -/
theorem generatedAxisGlobal_griessForm_sparse_coordinates
    {ι : Type*} [Fintype ι] (x y : GriessSpace)
    (c : ι → ℝ) (f : ι → GriessShortIndex)
    (hy : (griessConwayEncode y).2.1 = ∑ j, c j • Pi.single (f j) (1 : ℝ)) :
    griessForm x y =
      (∑ i : Fin 24, ∑ j : Fin 24,
        (griessConwayEncode x).1 i j * (griessConwayEncode y).1 i j) +
      (∑ j, c j * (griessConwayEncode x).2.1 (f j)) +
      conwayTensorForm (griessConwayEncode x).2.2 (griessConwayEncode y).2.2 := by
  rw [griessForm_eq_conwayRawForm, conwayRawForm, conwayMatrixForm_eq_sum, hy,
    generatedAxisGlobal_sparse_pairing]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
