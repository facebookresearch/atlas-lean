/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthE7ConjugationData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthCertifiedMatrixGeneric

/-! The complete certified coordinate transport is an actual original Leech lattice isometry. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

/-- The actual rational physical coordinate transport. -/
def generatedTenthE7Matrix : Matrix (Fin 24) (Fin 24) ℝ :=
  generatedTwelfthCertifiedRealMatrix generatedTenthE7Numerator 2

/-- The complete physical and integral witnesses give an actual original lattice isometry. -/
def generatedTenthE7Isometry : leechIsomSubgroup :=
  generatedTwelfthMatrixIsometry generatedTenthE7Matrix
    generatedTenthE7Integral generatedTenthE7IntegralInverse
    (generatedTwelfth_certified_real_left _ 2 (by decide)
      generatedTenth_e7_conjugation_orthogonal_left)
    (generatedTwelfth_certified_real_right _ 2 (by decide)
      generatedTenth_e7_conjugation_orthogonal_right)
    (generatedTwelfth_certified_real_basis _ _ 2 (by decide)
      generatedTenth_e7_conjugation_basis)
    generatedTenth_e7_conjugation_integral_inverse

/-- The actual isometry retains every original coordinate of its specified matrix. -/
theorem generatedTenth_e7_isometry_apply (v : Fin 24 → ℝ) :
    generatedTenthE7Isometry.val v = generatedTenthE7Matrix *ᵥ v := rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
