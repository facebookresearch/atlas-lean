/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFourthSelectedShortData

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsPreferredMaskFastActual

/-! Bounded kernel verification of complete original selected inverse preferred-Q images. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 1000000000

/-- Every selected binary image retains the complete original source preferred mask. -/
theorem generatedAxisGlobalOddFourthSelectedShortBinary_01_03 (i : Fin 448) :
    generatedAxisGlobalQMaskVector (generatedAxisGlobalOddFourthInverseMaskColumns 1)
      (generatedAxisGlobalShortMask (generatedAxisGlobalOddFourthSelectedTarget
        ⟨1448+i.val, by omega⟩)) =
    generatedAxisGlobalShortMask (generatedAxisGlobalOddFourthSelectedSource 1
      ⟨1448+i.val, by omega⟩) := by
  have h : ∀ i : Fin 448, generatedAxisGlobalQMaskVector
      (generatedAxisGlobalOddFourthInverseMaskColumns 1)
      (generatedAxisGlobalShortMask (generatedAxisGlobalOddFourthSelectedTarget
        ⟨1448+i.val, by omega⟩)) =
      generatedAxisGlobalShortMask (generatedAxisGlobalOddFourthSelectedSource 1
        ⟨1448+i.val, by omega⟩) := by
    simp_rw [← generatedAxisGlobalPreferredShortMaskFast_actual]
    decide +kernel
  exact h i

/-- Every selected central coefficient is checked in the original preferred section. -/
theorem generatedAxisGlobalOddFourthSelectedShortPhase_01_03 (i : Fin 448) :
    (if (generatedAxisGlobalQMaskCentral (generatedAxisGlobalOddFourthInverseMaskRows 1)
      (generatedAxisGlobalOddFourthInverseMaskCoefficients 1)
      (generatedAxisGlobalShortMask (generatedAxisGlobalOddFourthSelectedTarget
        ⟨1448+i.val, by omega⟩))).testBit 0 then (1 : ZMod 2) else 0) =
      generatedAxisGlobalOddFourthSelectedPhase 1 ⟨1448+i.val, by omega⟩ := by
  have h : ∀ i : Fin 448,
      (if (generatedAxisGlobalQMaskCentral (generatedAxisGlobalOddFourthInverseMaskRows 1)
        (generatedAxisGlobalOddFourthInverseMaskCoefficients 1)
        (generatedAxisGlobalShortMask (generatedAxisGlobalOddFourthSelectedTarget
          ⟨1448+i.val, by omega⟩))).testBit 0 then (1 : ZMod 2) else 0) =
      generatedAxisGlobalOddFourthSelectedPhase 1 ⟨1448+i.val, by omega⟩ := by
    simp_rw [← generatedAxisGlobalPreferredShortMaskFast_actual]
    decide +kernel
  exact h i

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
