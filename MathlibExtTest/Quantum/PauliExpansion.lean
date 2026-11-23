/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Quantum.PauliExpansion

/-!
# Tests: Pauli expansion of Hermitian matrices
-/

@[expose] public section

open scoped BigOperators
open MathlibExt.Quantum.PauliXZ
namespace MathlibExtTest.Quantum.PauliExpansion

set_option autoImplicit false

open MathlibExt.Quantum.PauliExpansion

#print axioms sum_pauliCoeff_smul_hermPauli
#print axioms trace_hermPauli_mul_hermPauli
#print axioms pauliTest_acceptance_eq
#print axioms sum_linearMap_eq_sum_pauliCoeff

/-- The identity has a single unit Pauli coefficient. -/
theorem pauliCoeff_one_zero (k : ℕ) :
    pauliCoeff (1 : Matrix (Fin k → ZMod 2) (Fin k → ZMod 2) ℂ) 0 0 = 1 := by
  unfold pauliCoeff
  have hHerm : hermPauli (0 : Fin k → ZMod 2) (0 : Fin k → ZMod 2) = 1 := by
    unfold hermPauli
    have hsum : (∑ i, ((0 : Fin k → ZMod 2) i).val * ((0 : Fin k → ZMod 2) i).val) = 0 := by
      simp
    rw [hsum, pow_zero, one_smul]
    ext y x
    rw [pauliXZ_apply]
    have hdot : ((0 : Fin k → ZMod 2) ⬝ᵥ x) = 0 := zero_dotProduct x
    rw [hdot, add_zero]
    simp only [ZMod.val_zero, pow_zero]
    rw [Matrix.one_apply]
  rw [hHerm, mul_one, Matrix.trace_one]
  have hcard : Fintype.card (Fin k → ZMod 2) = 2 ^ k := by
    rw [Fintype.card_fun, ZMod.card, Fintype.card_fin]
  rw [hcard]
  push_cast
  exact div_self (pow_ne_zero k (by norm_num : (2 : ℂ) ≠ 0))

end MathlibExtTest.Quantum.PauliExpansion
