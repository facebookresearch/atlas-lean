/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthPartialPauliData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthSpinCircuit

/-! Finite integer phase vectors and bounded anchor evaluations for the actual spin stages. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

/-- The finite signed affine phase vector determined by the genuine stage Pauli operators. -/
def generatedSixthPartialPhaseInteger (k : Fin 9) : NortonUIntegerVector := fun n =>
  let t := golayLabelCoefficients n + golayLabelCoefficients (generatedSixthPartialAnchor k)
  if generatedSixthAffineModulationMatrix (generatedSixthPartialPure k) *ᵥ t = 0 then
    nortonUIntegerSign (spinPhase (generatedSixthAffinePauliProduct
      (fun j => generatedSixthSpinPauliCache j k) (generatedSixthPartialProjection k *ᵥ t))
      (golayLabelCoefficients (generatedSixthPartialAnchor k))) else 0

/-- The actual integer operation at every step of the original word. -/
def generatedSixthPartialIntegerStep : Fin 8 → NortonUIntegerVector → NortonUIntegerVector :=
  ![generatedSixthIntegerPermutation 0, nortonUIntegerXi,
    generatedSixthIntegerPermutation 0, generatedSixthIntegerPermutation 1,
    generatedSixthIntegerPermutation 0, nortonUIntegerXi,
    generatedSixthIntegerPermutation 1, nortonUIntegerXi]

/-- The exact denominator contributed by the next original operator. -/
def generatedSixthPartialDenominator : Fin 8 → ℕ := ![1,8,1,1,1,8,1,8]

/-- The bounded integer anchor sum from the preceding genuine affine phase vector. -/
def generatedSixthPartialAnchorNumerator (k : Fin 8) : ℤ :=
  generatedSixthPartialIntegerStep k
    (generatedSixthPartialPhaseInteger (Fin.castSucc k))
    (generatedSixthPartialAnchor k.succ)

set_option maxHeartbeats 4000000 in
-- Check five single-coordinate evaluations and three original 64-term Gaussian sums.
/-- The actual source operators have these exact signed anchor numerators. -/
theorem generatedSixth_partial_anchor_certificate (k : Fin 8) :
    generatedSixthPartialAnchorNumerator k = (![1,-2,1,1,1,-4,-1,-4] k : ℤ) := by
  fin_cases k <;> decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
