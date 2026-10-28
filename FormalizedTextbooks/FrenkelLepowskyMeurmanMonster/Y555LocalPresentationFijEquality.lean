/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Corrected local F12=F13 from original C322 relators and a kernel-checked finite derivation.
Source: L.H. Soicher, Cambridge PhD thesis (1985), Chapter Y, printed pp.49–50,
DOI 10.17863/CAM.110463. The finite word derivation is independently reconstructed. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationTCContextRecognition
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationTCContextTarget
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationE7HTransporter

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The corrected seven-letter longest words agree in the original local source presentation. -/
theorem y322E7Word12_eq_word13 :
    PresentedGroup.mk y322Relations y322E7Word12 =
      PresentedGroup.mk y322Relations y322E7Word13 := by
  have h := y322TCContextProgram_valid 28529
  unfold Y322WordEquation.Valid at h
  rw [y322TCContext_target_left_value, y322TCContext_target_right_value,
    y322TransportH38539_value] at h
  exact mul_inv_eq_one.mp h

/-- The same genuine local consequence holds under the restricted independent Y555 map. -/
theorem y322E7Word12_eq_word13_in_Y555 :
    y322IntoY555 (PresentedGroup.mk y322Relations y322E7Word12) =
      y322IntoY555 (PresentedGroup.mk y322Relations y322E7Word13) := by
  exact congrArg y322IntoY555 y322E7Word12_eq_word13

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
