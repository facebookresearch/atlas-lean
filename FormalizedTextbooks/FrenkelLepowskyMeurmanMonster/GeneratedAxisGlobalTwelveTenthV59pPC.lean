/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTenthV59pChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTenthOddChunks

/-! # Pairing parts (odd short terms of the source, tensor) of the Tenth identification T59+
    (gtenth) -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- Odd part `oddLZ`, chunk group 0. -/
theorem tv59p_hb0 : oddLZT 64 true tv59pGX (OctadDense.octChunkTerms tv59pHC0) = 6488 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part `oddLZ`, chunk group 1. -/
theorem tv59p_hb1 : oddLZT 64 true tv59pGX (OctadDense.octChunkTerms tv59pHC1) = 4606 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part `oddLZ`, chunk group 2. -/
theorem tv59p_hb2 : oddLZT 64 true tv59pGX (OctadDense.octChunkTerms tv59pHC2) = 5464 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part `oddLZ`, chunk group 3. -/
theorem tv59p_hb3 : oddLZT 64 true tv59pGX (OctadDense.octChunkTerms tv59pHC3) = 4802 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part `oddLZ`, chunk group 4. -/
theorem tv59p_hb4 : oddLZT 64 true tv59pGX (OctadDense.octChunkTerms tv59pHC4) = 5080 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part `oddLZ`, chunk group 5. -/
theorem tv59p_hb5 : oddLZT 64 true tv59pGX (OctadDense.octChunkTerms tv59pHC5) = 5748 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part `oddLZ`, chunk group 6. -/
theorem tv59p_hb6 : oddLZT 64 true tv59pGX (OctadDense.octChunkTerms tv59pHC6) = 6540 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part `oddLZ`, chunk group 7. -/
theorem tv59p_hb7 : oddLZT 64 true tv59pGX (OctadDense.octChunkTerms tv59pHC7) = 6848 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part `oddLZ`, chunk group 8. -/
theorem tv59p_hb8 : oddLZT 64 true tv59pGX (OctadDense.octChunkTerms tv59pHC8) = 7472 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part `oddLZ`, chunk group 9. -/
theorem tv59p_hb9 : oddLZT 64 true tv59pGX (OctadDense.octChunkTerms tv59pHC9) = 5000 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part `oddLZ`, chunk group 10. -/
theorem tv59p_hb10 : oddLZT 64 true tv59pGX (OctadDense.octChunkTerms tv59pHC10) = 4728 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part `oddLZ`, chunk group 11. -/
theorem tv59p_hb11 : oddLZT 64 true tv59pGX (OctadDense.octChunkTerms tv59pHC11) = 1480 := by
  decide +kernel

/-- The odd part `oddLZ` of the pairing (sum of the chunk groups). -/
theorem tv59p_hb : oddLZ 64 true tv59pGX tv59pL = 6488 + 4606 + 5464 + 4802 + 5080 + 5748 + 6540 +
    6848 + 7472 + 5000 + 4728 + 1480 := by
  rw [oddLZ_ofList 64 true tv59pGX tv59pL tv59pHT rfl]
  simp only [tv59pHT, tv59pHC, octChunkTerms_append, oddLZT_append, tv59p_hb0, tv59p_hb1,
      tv59p_hb2, tv59p_hb3, tv59p_hb4, tv59p_hb5, tv59p_hb6, tv59p_hb7, tv59p_hb8, tv59p_hb9,
      tv59p_hb10, tv59p_hb11]

set_option maxRecDepth 100000 in
/-- The tensor part of the pairing. -/
theorem tv59p_hc : tdotM 64 (trialityTensorT 64 (!true) tv59pHX) tv59pGX = 128512 := by
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
