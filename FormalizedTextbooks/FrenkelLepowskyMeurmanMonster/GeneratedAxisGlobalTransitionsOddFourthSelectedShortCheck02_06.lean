/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFourthSelectedShortData

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsPreferredMaskFastActual
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinFastQMaskCentral

/-! Bounded kernel verification of complete original selected inverse preferred-Q images. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 1000000000

/-- Every selected binary image retains the complete original source preferred mask. -/
theorem generatedAxisGlobalOddFourthSelectedShortBinary_02_06 (i : Fin 448) :
    generatedAxisGlobalQMaskVector (generatedAxisGlobalOddFourthInverseMaskColumns 2)
      (generatedAxisGlobalShortMask (generatedAxisGlobalOddFourthSelectedTarget
        ⟨2792+i.val, by omega⟩)) =
    generatedAxisGlobalShortMask (generatedAxisGlobalOddFourthSelectedSource 2
      ⟨2792+i.val, by omega⟩) := by
  have h : ∀ i : Fin 448, generatedAxisGlobalQMaskVector
      (generatedAxisGlobalOddFourthInverseMaskColumns 2)
      (generatedAxisGlobalShortMask (generatedAxisGlobalOddFourthSelectedTarget
        ⟨2792+i.val, by omega⟩)) =
      generatedAxisGlobalShortMask (generatedAxisGlobalOddFourthSelectedSource 2
        ⟨2792+i.val, by omega⟩) := by
    simp_rw [← generatedAxisGlobalPreferredShortMaskFast_actual]
    decide +kernel
  exact h i

/-- Every selected central coefficient is checked in the original preferred section. -/
theorem generatedAxisGlobalOddFourthSelectedShortPhase_02_06 (i : Fin 448) :
    (if (generatedAxisGlobalQMaskCentral (generatedAxisGlobalOddFourthInverseMaskRows 2)
      (generatedAxisGlobalOddFourthInverseMaskCoefficients 2)
      (generatedAxisGlobalShortMask (generatedAxisGlobalOddFourthSelectedTarget
        ⟨2792+i.val, by omega⟩))).testBit 0 then (1 : ZMod 2) else 0) =
      generatedAxisGlobalOddFourthSelectedPhase 2 ⟨2792+i.val, by omega⟩ := by
  have h : ∀ i : Fin 448,
      (if (generatedAxisGlobalQMaskCentral (generatedAxisGlobalOddFourthInverseMaskRows 2)
        (generatedAxisGlobalOddFourthInverseMaskCoefficients 2)
        (generatedAxisGlobalShortMask (generatedAxisGlobalOddFourthSelectedTarget
          ⟨2792+i.val, by omega⟩))).testBit 0 then (1 : ZMod 2) else 0) =
      generatedAxisGlobalOddFourthSelectedPhase 2 ⟨2792+i.val, by omega⟩ := by
    simp_rw [← generatedAxisGlobalPreferredShortMaskFast_actual,
      ← generatedNinth_lower_spin_fast_q_mask_central]
    decide +kernel
  exact h i

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
