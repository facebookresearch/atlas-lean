/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthXiFastTensor

/-! Four literal physical columns suffice in each row of the original conjugated Xi matrix. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- The four original tetrad columns, transported back by the genuine C word. -/
def generatedSixthXiPhysicalColumn (i : Fin 24) (a : Fin 4) : Fin 24 :=
  sixthFrameOrbitCInverse (Fin.ofNat 24 (4 * ((sixthFrameOrbitCForward i).val / 4) + a.val))

/-- The original cleared matrix coefficient at the displayed physical column. -/
def generatedSixthXiPhysicalWeight (i : Fin 24) (a : Fin 4) : ℤ :=
  sixthFrameOrbitSpatialNumerator 14 i (generatedSixthXiPhysicalColumn i a)

set_option maxHeartbeats 4000000 in
-- Compare every original 24-by-24 matrix entry to the four displayed columns.
/-- The complete original physical matrix is exactly the sum of its four column indicators. -/
theorem generatedSixth_xi_physical_support :
    ∀ i : Fin 24, ∀ j : Fin 24,
      sixthFrameOrbitSpatialNumerator 14 i j =
        ∑ a : Fin 4, if j = generatedSixthXiPhysicalColumn i a then
          generatedSixthXiPhysicalWeight i a else 0 := by
  decide +kernel

/-- Arbitrary integer spin data may use four columns without dropping any original term. -/
theorem generatedSixth_xi_physical_sum (i : Fin 24) (f : Fin 24 → ℤ) :
    (∑ j : Fin 24, sixthFrameOrbitSpatialNumerator 14 i j * f j) =
      ∑ a : Fin 4, generatedSixthXiPhysicalWeight i a *
        f (generatedSixthXiPhysicalColumn i a) := by
  simp_rw [generatedSixth_xi_physical_support, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  simp only [ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
