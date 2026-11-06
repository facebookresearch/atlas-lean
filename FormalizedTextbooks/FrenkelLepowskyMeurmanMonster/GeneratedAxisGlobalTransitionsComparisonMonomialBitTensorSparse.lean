/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsComparisonMonomialBitTensor

/-! Complete original bounded spin tensor formula with a proved zero-input phase guard. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option autoImplicit false

/-- Evaluate the full original phase only at a genuine nonzero tensor input. -/
def generatedAxisGlobalComparisonMonomialBitTensorSparse (k : Fin 8)
    (T : GeneratedAxisGlobalRationalTensor) (a : Fin 4096) (i : Fin 24) : ℚ :=
  let z := T (generatedAxisGlobalSpinLabel (generatedAxisGlobalComparisonMonomialBitPull k a))
    ((((generatedAxisGlobalComparisonMonomialWord k).map
      generatedFourthMonomialPermutationLetter).prod).val.symm i)
  if z = 0 then 0 else
    (generatedAxisGlobalIntSign (generatedAxisGlobalComparisonMonomialBitPhase k a) : ℚ) * z

/-- Every guarded tensor coefficient equals the complete original phase-correct bit formula. -/
theorem generatedAxisGlobalComparisonMonomialBitTensorSparse_eq (k : Fin 8)
    (T : GeneratedAxisGlobalRationalTensor) :
    generatedAxisGlobalComparisonMonomialBitTensorSparse k T =
      generatedAxisGlobalComparisonMonomialBitTensor k T := by
  funext a i
  unfold generatedAxisGlobalComparisonMonomialBitTensorSparse generatedAxisGlobalComparisonMonomialBitTensor
  dsimp only
  split_ifs with h
  · rw [h,mul_zero]
  · rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
