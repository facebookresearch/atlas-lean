/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Quantum.PauliXZ

@[expose] public section

open MathlibExt.Quantum.PauliXZ

/-- The identity Pauli (a = b = 0) fixes the zero basis state. -/
example : pauliXZ (0 : Fin 1 → ZMod 2) 0 0 0 = 1 := by
  simp

/-- On one qubit, `Z * X = -(X Z)`: with `Z = X^0 Z^1` and `X = X^1 Z^0` the product rule
picks up the phase `(-1) ^ (1 ⬝ᵥ 1) = -1`. -/
example : pauliXZ (0 : Fin 1 → ZMod 2) 1 * pauliXZ 1 0 = -pauliXZ 1 1 := by
  rw [pauliXZ_mul]
  have h : ((1 : Fin 1 → ZMod 2) ⬝ᵥ 1).val = 1 := by decide
  rw [h, zero_add, add_zero, pow_one, neg_one_smul]

/-- On one qubit, `X * Z = X Z`: the phase `(-1) ^ (0 ⬝ᵥ 0)` is `1`. -/
example : pauliXZ (1 : Fin 1 → ZMod 2) 0 * pauliXZ 0 1 = pauliXZ 1 1 := by
  rw [pauliXZ_mul]
  have h : ((0 : Fin 1 → ZMod 2) ⬝ᵥ 0).val = 0 := by decide
  rw [h, add_zero, zero_add, pow_zero, one_smul]

end
