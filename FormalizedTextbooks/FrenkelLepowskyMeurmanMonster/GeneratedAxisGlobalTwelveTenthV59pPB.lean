/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTenthV59pChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTenthOddChunks

/-! # Pairing part (odd short terms of the target) of the Tenth identification T59+ (gtenth) -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- Odd part `oddWZ`, chunk group 0. -/
theorem tv59p_ha0 : oddWZT 64 true tv59pHX (OctadDense.octChunkTerms tv59pGC0) = 6488 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part `oddWZ`, chunk group 1. -/
theorem tv59p_ha1 : oddWZT 64 true tv59pHX (OctadDense.octChunkTerms tv59pGC1) = 4606 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part `oddWZ`, chunk group 2. -/
theorem tv59p_ha2 : oddWZT 64 true tv59pHX (OctadDense.octChunkTerms tv59pGC2) = 5464 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part `oddWZ`, chunk group 3. -/
theorem tv59p_ha3 : oddWZT 64 true tv59pHX (OctadDense.octChunkTerms tv59pGC3) = 4802 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part `oddWZ`, chunk group 4. -/
theorem tv59p_ha4 : oddWZT 64 true tv59pHX (OctadDense.octChunkTerms tv59pGC4) = 5080 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part `oddWZ`, chunk group 5. -/
theorem tv59p_ha5 : oddWZT 64 true tv59pHX (OctadDense.octChunkTerms tv59pGC5) = 5748 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part `oddWZ`, chunk group 6. -/
theorem tv59p_ha6 : oddWZT 64 true tv59pHX (OctadDense.octChunkTerms tv59pGC6) = 6540 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part `oddWZ`, chunk group 7. -/
theorem tv59p_ha7 : oddWZT 64 true tv59pHX (OctadDense.octChunkTerms tv59pGC7) = 6848 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part `oddWZ`, chunk group 8. -/
theorem tv59p_ha8 : oddWZT 64 true tv59pHX (OctadDense.octChunkTerms tv59pGC8) = 7472 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part `oddWZ`, chunk group 9. -/
theorem tv59p_ha9 : oddWZT 64 true tv59pHX (OctadDense.octChunkTerms tv59pGC9) = 5000 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part `oddWZ`, chunk group 10. -/
theorem tv59p_ha10 : oddWZT 64 true tv59pHX (OctadDense.octChunkTerms tv59pGC10) = 4728 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part `oddWZ`, chunk group 11. -/
theorem tv59p_ha11 : oddWZT 64 true tv59pHX (OctadDense.octChunkTerms tv59pGC11) = 1480 := by
  decide +kernel

/-- The odd part `oddWZ` of the pairing (sum of the chunk groups). -/
theorem tv59p_ha : oddWZ 64 true tv59pHX tv59pW = 6488 + 4606 + 5464 + 4802 + 5080 + 5748 + 6540 +
    6848 + 7472 + 5000 + 4728 + 1480 := by
  rw [oddWZ_ofList 64 true tv59pHX tv59pW tv59pGT rfl]
  simp only [tv59pGT, tv59pGC, octChunkTerms_append, oddWZT_append, tv59p_ha0, tv59p_ha1,
      tv59p_ha2, tv59p_ha3, tv59p_ha4, tv59p_ha5, tv59p_ha6, tv59p_ha7, tv59p_ha8, tv59p_ha9,
      tv59p_ha10, tv59p_ha11]

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
