/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthE7OrbitMonomialPermutation
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthE7XiCorrectionTransportData

/-! Whole original-coordinate witnesses for the genuine monomial root-orbit generator. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators Matrix
set_option maxRecDepth 100000

/-- The exact original Golay codeword used by the monomial root-orbit generator. -/
def generatedTenthE7OrbitMonoCode : golayCode :=
  ⟨golayEncoder (golayLabelCoefficients 1410), ⟨golayLabelCoefficients 1410, rfl⟩⟩

/-- The complete signed monomial matrix in genuine physical column convention. -/
def generatedTenthE7OrbitMonoMatrix : Matrix (Fin 24) (Fin 24) ℤ := fun i j =>
  (if generatedTenthE7OrbitMonoCode.val i = 0 then 1 else -1) *
    (if j = generatedTenthE7OrbitMonoInverse i then 1 else 0)

/-- The actual norm-twelve vector and normal root are both fixed positively. -/
theorem generatedTenth_e7_orbit_mono_vectors :
    generatedTenthE7OrbitMonoMatrix *ᵥ generatedTenthE7XiLine = generatedTenthE7XiLine ∧
      generatedTenthE7OrbitMonoMatrix *ᵥ generatedTenthE7XiNormal =
        generatedTenthE7XiNormal := by
  decide +kernel

/-- The whole physical monomial matrix commutes with the complete E7 projector. -/
theorem generatedTenth_e7_orbit_mono_projection_commute :
    generatedTenthE7OrbitMonoMatrix * generatedTenthE7XiProjection =
      generatedTenthE7XiProjection * generatedTenthE7OrbitMonoMatrix := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
