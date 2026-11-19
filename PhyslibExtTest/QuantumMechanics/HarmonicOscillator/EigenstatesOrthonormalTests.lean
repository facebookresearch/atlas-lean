/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.QuantumMechanics.HarmonicOscillator.EigenstatesOrthonormal
public import PhyslibExt.SpaceAndTime.Space.Integrals.Prod

@[expose] public section

/-!
# Client tests for QHO eigenstate orthonormality

Smoke tests applying `eigenstates_orthonormal_of_oneDim` and
`Space.integral_prod_coord`, plus axiom audits for the new API.
-/

set_option autoImplicit false

open InnerProductSpace KroneckerDelta MeasureTheory
open QuantumMechanics.HarmonicOscillator

/-- Eigenstates are normalized. -/
example (Q : QuantumMechanics.HarmonicOscillator 1) (n : Fin 1 → ℕ) :
    ⟪(Q.eigenstate n : Q.HS), Q.eigenstate n⟫_ℂ = 1 := by
  rw [eigenstates_orthonormal_of_oneDim]
  simp [kroneckerDelta]

/-- The integral-splitting lemma applies to constant functions. -/
example : (∫ _x : Space 1, ∏ _i : Fin 1, (1 : ℂ) ∂volume)
    = ∏ _i : Fin 1, ∫ _t : ℝ, (1 : ℂ) ∂volume :=
  Space.integral_prod_coord (fun _ _ => 1)

#print axioms Space.integral_prod_coord
#print axioms QuantumMechanics.HarmonicOscillator.oneDim
#print axioms QuantumMechanics.HarmonicOscillator.eigenfunction_eq_prod_oneDim
#print axioms QuantumMechanics.HarmonicOscillator.eigenstates_orthonormal_of_oneDim
