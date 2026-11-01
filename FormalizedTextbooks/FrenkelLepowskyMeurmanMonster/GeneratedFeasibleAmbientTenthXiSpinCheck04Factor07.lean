/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleAmbientTenthSignDataB
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleAmbientTenthFastXi

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
-- Labels 0 to 511 of the Gaussian are checked.
private theorem xi0 : ∀ a : Fin 512,
    generatedFeasibleAmbientTenthXi (generatedFeasibleAmbientTenthSignSpin 4 7)
        (generatedFeasibleAmbientTenthBlockLabel 0 a) =
      8 * generatedFeasibleAmbientTenthSpin 5 7 (generatedFeasibleAmbientTenthBlockLabel 0 a) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
-- Labels 512 to 1023 of the Gaussian are checked.
private theorem xi1 : ∀ a : Fin 512,
    generatedFeasibleAmbientTenthXi (generatedFeasibleAmbientTenthSignSpin 4 7)
        (generatedFeasibleAmbientTenthBlockLabel 1 a) =
      8 * generatedFeasibleAmbientTenthSpin 5 7 (generatedFeasibleAmbientTenthBlockLabel 1 a) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
-- Labels 1024 to 1535 of the Gaussian are checked.
private theorem xi2 : ∀ a : Fin 512,
    generatedFeasibleAmbientTenthXi (generatedFeasibleAmbientTenthSignSpin 4 7)
        (generatedFeasibleAmbientTenthBlockLabel 2 a) =
      8 * generatedFeasibleAmbientTenthSpin 5 7 (generatedFeasibleAmbientTenthBlockLabel 2 a) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
-- Labels 1536 to 2047 of the Gaussian are checked.
private theorem xi3 : ∀ a : Fin 512,
    generatedFeasibleAmbientTenthXi (generatedFeasibleAmbientTenthSignSpin 4 7)
        (generatedFeasibleAmbientTenthBlockLabel 3 a) =
      8 * generatedFeasibleAmbientTenthSpin 5 7 (generatedFeasibleAmbientTenthBlockLabel 3 a) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
-- Labels 2048 to 2559 of the Gaussian are checked.
private theorem xi4 : ∀ a : Fin 512,
    generatedFeasibleAmbientTenthXi (generatedFeasibleAmbientTenthSignSpin 4 7)
        (generatedFeasibleAmbientTenthBlockLabel 4 a) =
      8 * generatedFeasibleAmbientTenthSpin 5 7 (generatedFeasibleAmbientTenthBlockLabel 4 a) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
-- Labels 2560 to 3071 of the Gaussian are checked.
private theorem xi5 : ∀ a : Fin 512,
    generatedFeasibleAmbientTenthXi (generatedFeasibleAmbientTenthSignSpin 4 7)
        (generatedFeasibleAmbientTenthBlockLabel 5 a) =
      8 * generatedFeasibleAmbientTenthSpin 5 7 (generatedFeasibleAmbientTenthBlockLabel 5 a) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
-- Labels 3072 to 3583 of the Gaussian are checked.
private theorem xi6 : ∀ a : Fin 512,
    generatedFeasibleAmbientTenthXi (generatedFeasibleAmbientTenthSignSpin 4 7)
        (generatedFeasibleAmbientTenthBlockLabel 6 a) =
      8 * generatedFeasibleAmbientTenthSpin 5 7 (generatedFeasibleAmbientTenthBlockLabel 6 a) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
-- Labels 3584 to 4095 of the Gaussian are checked.
private theorem xi7 : ∀ a : Fin 512,
    generatedFeasibleAmbientTenthXi (generatedFeasibleAmbientTenthSignSpin 4 7)
        (generatedFeasibleAmbientTenthBlockLabel 7 a) =
      8 * generatedFeasibleAmbientTenthSpin 5 7 (generatedFeasibleAmbientTenthBlockLabel 7 a) := by
  decide +kernel

/-- The Gaussian of root-two factor 7 at stage 4. -/
theorem generatedFeasibleAmbientTenth_xi_spin_check04_07 : ∀ a : Fin 4096,
    generatedFeasibleAmbientTenthXi (generatedFeasibleAmbientTenthSignSpin 4 7) a = 8 *
        generatedFeasibleAmbientTenthSpin 5 7 a := by
  apply generatedFeasibleAmbientTenth_fin4096_blocks
  intro q
  fin_cases q
  · exact xi0
  · exact xi1
  · exact xi2
  · exact xi3
  · exact xi4
  · exact xi5
  · exact xi6
  · exact xi7

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
