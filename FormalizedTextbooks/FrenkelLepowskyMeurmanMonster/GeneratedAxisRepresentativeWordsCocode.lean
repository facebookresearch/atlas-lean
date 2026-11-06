/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The exact cocode sign used to correct literal compact permutation words. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRepresentativeWordsPlan

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix BigOperators

/-- A diagonal binary quadratic polynomial is the actual linear cocode character. -/
theorem representativeQuadratic_diagonal (δ t : SpinIndex) :
    monsterMonomialQuadratic (Matrix.diagonal δ) t = spinDot δ t := by
  rw [representativeQuadratic_dot]
  simp only [dotProduct, Matrix.mulVec_diagonal, spinDot]
  apply Finset.sum_congr rfl
  intro i _
  have hc : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide +kernel
  obtain h | h := hc (t i) <;> simp [h]

/-- Positive source cocodes have the full diagonal operator certificate, with central sign zero. -/
theorem representativeSpinCertificate_cocode (δ : SpinIndex) :
    representativeSpinCertificate (spinHolomorphIncl (sourceQCocode δ)) 1
      (Matrix.diagonal δ) := by
  intro f t
  rw [representativeQuadratic_diagonal, Matrix.one_mulVec]
  exact monsterSourceQCocode_spin δ f t

/-- The cocode correction in the actual defining fiber has the same full spin certificate. -/
theorem representativeSpinCertificate_cocodeFiber (δ : SpinIndex) :
    representativeSpinCertificate (localFiberIncl (sourceQCocode δ)).val.1 1
      (Matrix.diagonal δ) := representativeSpinCertificate_cocode δ

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
