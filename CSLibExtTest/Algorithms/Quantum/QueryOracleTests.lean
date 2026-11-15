/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Quantum.QueryOracle

@[expose] public section

/-!
# Tests for the quantum query oracle

Direct reductions check that the oracle flips the target bit exactly where `f x = true`.
-/

open Cslib.Quantum

/-- The constant-true oracle flips the target bit `false` to `true`. -/
example : queryOracle (fun _ : Fin 2 => true) (1, false) = (1, true) := rfl

/-- The constant-true oracle flips the target bit `true` to `false`. -/
example : queryOracle (fun _ : Fin 2 => true) (1, true) = (1, false) := rfl

/-- The constant-false oracle leaves the state unchanged. -/
example : queryOracle (fun _ : Fin 2 => false) (1, false) = (1, false) := rfl

/-- The constant-false oracle leaves a `true` target unchanged. -/
example : queryOracle (fun _ : Fin 2 => false) (0, true) = (0, true) := rfl

/-- A non-constant oracle flips the target only where `f x = true`. -/
example : queryOracle (fun x : Fin 2 => decide (x = 0)) (0, false) = (0, true) := rfl

/-- At a register value with `f x = false`, the same oracle leaves the target alone. -/
example : queryOracle (fun x : Fin 2 => decide (x = 0)) (1, false) = (1, false) := rfl

/-- The XOR form computes the flipped target bit. -/
example : queryOracle (fun _ : Fin 3 => true) (2, true) = (2, false) := by
  rw [queryOracle_apply]
  rfl

/-- Querying twice with the constant-true oracle restores the state. -/
example : queryOracle (fun _ : Fin 2 => true) (queryOracle (fun _ : Fin 2 => true) (1, false)) =
    (1, false) :=
  queryOracle_involutive _ _

/-- The oracle keeps the register value. -/
example : (queryOracle (fun _ : Fin 2 => true) (1, false)).1 = 1 :=
  queryOracle_fst _ _

end
