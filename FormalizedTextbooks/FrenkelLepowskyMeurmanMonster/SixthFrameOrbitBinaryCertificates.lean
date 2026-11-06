/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.SixthFrameOrbitDataIntegral
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechOrbitActions

/-! Exact reductions of the integral basis matrices, with the original column orientation. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

set_option maxRecDepth 10000 in
set_option maxHeartbeats 40000000 in
-- Decode sixteen complete basis actions in the actual hyperbolic coordinates.
/-- The monomial column catalogue is precisely the parity of the actual integral basis action. -/
theorem sixthFrameOrbit_binary_check : ∀ k : Fin 16,
    sixthFrameOrbitColumnMatrix (sixthFrameOrbitMonomialColumns k) =
      leechHyperbolicInverse * (sixthFrameOrbitIntegral k).map (Int.castRingHom (ZMod 2)) *
        leechHyperbolicMatrix := by
  decide +kernel

/-- The fourteen original orbit generators use the matching certified monomial columns. -/
theorem sixthFrameOrbit_monomial_columns_check : ∀ k : Fin 14,
    sixthFrameOrbitMonomialColumns (Fin.castAdd 2 k) =
      sixthFrameOrbitColumns (Fin.castAdd 1 k) := by
  decide +kernel

set_option maxHeartbeats 12000000 in
-- Check the complete conjugated actual Xi matrix in the same left-action orientation.
/-- The final orbit generator's columns are the actual inverse-C, Xi, C matrix product. -/
theorem sixthFrameOrbit_xi_columns_check :
    sixthFrameOrbitColumnMatrix (sixthFrameOrbitColumns 14) =
      sixthFrameOrbitColumnMatrix (sixthFrameOrbitMonomialColumns 15) *
        omegaOrbitBinaryMatrices 0 *
        sixthFrameOrbitColumnMatrix (sixthFrameOrbitMonomialColumns 14) := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
